"""
    mutable struct AbstractGlobal
        t::Any     # analyzed type
        iscd::Bool # whether this abstract global variable is declarared as constant or not
    end

Wraps a global variable whose type is analyzed by abtract interpretation.
`AbstractGlobal` object will be actually evaluated into the context module, and a later
  analysis may refer to its type or alter it on another assignment.

!!! note
    The type of the wrapped global variable will be propagated only when in a toplevel frame,
      and thus we don't care about the analysis cache invalidation on a refinement of the
      wrapped global variable, since JET doesn't cache the toplevel frame.
"""
mutable struct AbstractGlobal
    # analyzed type
    t::Any
    iscd::Bool

    function AbstractGlobal(@nospecialize(t),
                            iscd::Bool,
                            )
        return new(t,
                   iscd,
                   )
    end
end

# branching on https://github.com/JuliaLang/julia/pull/41020
const IS_LATEST_INTERFACE = isdefined(CC, :MethodCallResult)
@static if IS_LATEST_INTERFACE

import .CC:
    bail_out_toplevel_call,
    bail_out_call,
    add_call_backedges!,
    MethodCallResult,
    ConstCallInfo,
    const_prop_entry_heuristic,
    const_prop_rettype_heuristic

# TODO:
# - report "too many method matched"
# - maybe "cound not identify method table for call" won't happen since we eagerly propagate bottom for e.g. undef var case, etc.

function CC.abstract_call_gf_by_type(interp::JETInterpreter, @nospecialize(f),
                                     fargs::Union{Nothing,Vector{Any}}, argtypes::Vector{Any}, @nospecialize(atype),
                                     sv::InferenceState, max_methods::Int = InferenceParams(interp).MAX_METHODS)
    ret = @invoke abstract_call_gf_by_type(interp::AbstractInterpreter, @nospecialize(f),
                                           fargs::Union{Nothing,Vector{Any}}, argtypes::Vector{Any}, @nospecialize(atype),
                                           sv::InferenceState, max_methods::Int)

    info = ret.info
    if isa(info, ConstCallInfo)
        info = info.call # unwrap to `MethodMatchInfo` or `UnionSplitInfo`
    end
    # report passes for no matching methods error
    report_pass!(NoMethodErrorReport, interp, sv, info, atype, argtypes)

    analyze_task_parallel_code!(interp, f, argtypes, sv)

    return ret
end

@doc """
    bail_out_toplevel_call(interp::JETInterpreter, ...)

An overload for `abstract_call_gf_by_type(interp::JETInterpreter, ...)`, which keeps
  inference on non-concrete call sites in a toplevel frame created by
  [`virtual_process`](@ref).
"""
function CC.bail_out_toplevel_call(interp::JETInterpreter, @nospecialize(sig), sv)
    return isa(sv.linfo.def, Module) && !isdispatchtuple(sig) && !istoplevel(interp, sv)
end

@doc """
    bail_out_call(interp::JETInterpreter, ...)

With this overload, `abstract_call_gf_by_type(interp::JETInterpreter, ...)` doesn't bail out
  inference even after the current return type grows up to `Any` and collects as much error
  points as possible.
Of course this slows down inference performance, but hoopefully it stays to be "practical"
  speed since the number of matching methods are limited beforehand.
"""
CC.bail_out_call(interp::JETInterpreter, @nospecialize(t), sv) = false

@doc """
    add_call_backedges!(interp::JETInterpreter, ...)

An overload for `abstract_call_gf_by_type(interp::JETInterpreter, ...)`, which always add
  backedges (even if a new method can't refine the return type grew up to `Any`).
This is because a new method definition always has a potential to change the JET analysis result.
"""
function CC.add_call_backedges!(interp::JETInterpreter,
                                @nospecialize(rettype),
                                edges::Vector{MethodInstance},
                                fullmatch::Vector{Bool}, mts::Vector{Core.MethodTable}, @nospecialize(atype),
                                sv::InferenceState)
    # a new method may refine analysis, so we always add backedges
    # if rettype === Any
    #     # for `NativeInterpreter`, we don't add backedges when a new method couldn't refine
    #     # (widen) this type
    #     return
    # end
    for edge in edges
        add_backedge!(edge, sv)
    end
    for (thisfullmatch, mt) in zip(fullmatch, mts)
        if !thisfullmatch
            # also need an edge to the method table in case something gets
            # added that did not intersect with any existing method
            add_mt_backedge!(mt, atype, sv)
        end
    end
end

function CC.abstract_call_method_with_const_args(interp::JETInterpreter, result::MethodCallResult,
                                                 @nospecialize(f), argtypes::Vector{Any}, match::MethodMatch,
                                                 sv::InferenceState, va_override::Bool)
    result, inf_result = @invoke abstract_call_method_with_const_args(interp::AbstractInterpreter, result::MethodCallResult,
                                                                      @nospecialize(f), argtypes::Vector{Any}, match::MethodMatch,
                                                                      sv::InferenceState, va_override::Bool)

    if isa(inf_result, InferenceResult)
        # successful constant prop', we also need to update reports
        update_reports!(interp, sv)
    end

    return result, inf_result
end

@doc """
    const_prop_entry_heuristic(interp::JETInterpreter, result::MethodCallResult, sv::InferenceState)

This overload for `abstract_call_method_with_const_args(interp::JETInterpreter, ...)` forces
constant prop' even if an inference result can't be improved anymore _with respect to the
return type_, e.g. when `result.rt` is already `Const`.
Especially, this overload implements an heuristic to force constant prop' when any error points
have been reported while the previous abstract method call without constant arguments.
The reason we want much more aggressive constant propagation by that heuristic is that it's
highly possible constant prop' can produce more accurate analysis result, by throwing away
false positive error reports by cutting off the unreachable control flow or detecting
must-reachable `throw` calls.
"""
function CC.const_prop_entry_heuristic(interp::JETInterpreter, result::MethodCallResult, sv::InferenceState)
    edge = result.edge # edge associated with the previous non-constant analysis
    if !isnothing(edge)
        # if any error has been reported within the previous `abstract_call_method` (associated with `edge`),
        # force constant prop' and hope it can cut-off false positives
        any(is_from_same_frame(sv.linfo, edge), interp.reports) && return true
    end
    return @invoke const_prop_entry_heuristic(interp::AbstractInterpreter, result::MethodCallResult, sv::InferenceState)
end

else # @static if IS_LATEST_INTERFACE

include("legacy/abstractinterpretation")

end # @static if IS_LATEST_INTERFACE

"""
    analyze_task_parallel_code!(interp::JETInterpreter, @nospecialize(f), argtypes::Vector{Any}, sv::InferenceState)

Adds special cased analysis pass for task parallelism (xref: <https://github.com/aviatesk/JET.jl/issues/114>).
In Julia's task parallelism implementation, parallel code is represented as closure and it's
  wrapped in a `Task` object. `NativeInterpreter` doesn't run type inference nor optimization
  on the body of those closures when compiling code that creates parallel tasks, but JET will
  try to run additional analysis pass by recurring into the closures.

!!! note
    JET won't do anything other than doing JET analysis, e.g. won't annotate return type
    of wrapped code block in order to not confuse the original `AbstractInterpreter` routine
    track <https://github.com/JuliaLang/julia/pull/39773> for the changes in native abstract
    interpretation routine.
"""
function analyze_task_parallel_code!(interp::JETInterpreter, @nospecialize(f), argtypes::Vector{Any}, sv::InferenceState)
    # TODO ideally JET should analyze a closure wrapped in a `Task` only when it's `schedule`d
    # but the `Task` construction may not happen in the same frame where it's `schedule`d
    # and so we may not be able to access to the closure at that point
    # as a compromise, JET now invokes the additional analysis on `Task` construction,
    # regardless of whether it's really `schedule`d or not
    if f === Task &&
       length(argtypes) ≥ 2 &&
       (v = argtypes[2]; v ⊑ Function)
        # if we encounter `Task(::Function)`, try to get its inner function and run analysis on it
        # the closure can be a nullary lambda that really doesn't depend on
        # the captured environment, and in that case we can retrieve it as
        # a function object, otherwise we will try to retrieve the type of the closure
        ft = (isa(v, Const) ? Core.Typeof(v.val) :
              isa(v, Core.PartialStruct) ? v.typ :
              isa(v, DataType) ? v :
              return)::Type
        analyze_additional_pass_by_type!(interp, Tuple{ft}, sv)
        return
    end
    return
end

# run additional interpretation with a new interpreter,
# and then append the reports to the original interpreter
function analyze_additional_pass_by_type!(interp::JETInterpreter, @nospecialize(tt::Type{<:Tuple}), sv::InferenceState)
    newinterp = JETInterpreter(interp)

    # in order to preserve the inference termination, we keep to use the current frame
    # and borrow the `AbstractInterpreter`'s cycle detection logic
    # XXX the additional analysis pass by `abstract_call_method` may involve various site-effects,
    # but what we're doing here is essentially equivalent to modifying the user code and inlining
    # the threaded code block as a usual code block, and thus the side-effects won't (hopefully)
    # confuse the abstract interpretation, which is supposed to terminate on any kind of code
    mm = get_single_method_match(tt, InferenceParams(newinterp).MAX_METHODS, get_world_counter(newinterp))
    result = abstract_call_method(newinterp, mm.method, mm.spec_types, mm.sparams, false, sv)

    rt = @static @isdefined(MethodCallResult) ? result.rt : first(result)

    # corresponding to the same logic in `analyze_frame!`
    if rt === Bottom
        if !isempty(newinterp.uncaught_exceptions)
            append!(newinterp.reports, newinterp.uncaught_exceptions)
        end
    end

    append!(interp.reports, newinterp.reports)
end

# works within inter-procedural context
function CC.abstract_call_method(interp::JETInterpreter, method::Method, @nospecialize(sig), sparams::SimpleVector, hardlimit::Bool, sv::InferenceState)
    ret = @invoke abstract_call_method(interp::AbstractInterpreter, method::Method, sig, sparams::SimpleVector, hardlimit::Bool, sv::InferenceState)

    update_reports!(interp, sv)

    return ret
end

function update_reports!(interp::JETInterpreter, sv::InferenceState)
    rs = interp.to_be_updated
    if !isempty(rs)
        vf = get_virtual_frame(interp, sv)
        for r in rs
            pushfirst!(r.vst, vf)
        end
        empty!(rs)
    end
end

@static if isdefined(CC, :abstract_invoke)

import .CC:
    abstract_invoke,
    InvokeCallInfo,
    instanceof_tfunc

@reportdef struct InvalidInvokeErrorReport <: InferenceErrorReport
    argtypes::Vector{Any}
end

function get_msg(::Type{InvalidInvokeErrorReport}, interp, sv::InferenceState, argtypes::Vector{Any})
    fallback_msg = "invalid invoke" # mostly because of runtime unreachable

    ft = widenconst(argtype_by_index(argtypes, 2))
    ft === Bottom && return fallback_msg
    t = argtype_by_index(argtypes, 3)
    (types, isexact, isconcrete, istype) = instanceof_tfunc(t)
    if types === Bottom
        if isa(t, Const)
            type = typeof(t.val)
            return "argument type should be `Type`-object (given `$type`)"
        end
        return fallback_msg
    end

    argtype = argtypes_to_type(argtype_tail(argtypes, 4))
    nargtype = typeintersect(types, argtype)
    @assert nargtype === Bottom
    return "actual argument type (`$argtype`) doesn't intersect with specified argument type (`$types`)"
end

function CC.abstract_invoke(interp::JETInterpreter, argtypes::Vector{Any}, sv::InferenceState)
    ret = @invoke abstract_invoke(interp::AbstractInterpreter, argtypes::Vector{Any}, sv::InferenceState)

    report_pass!(InvalidInvokeErrorReport, interp, sv, ret, argtypes)

    return ret
end

end # @static if isdefined(CC, :abstract_invoke)

function CC.abstract_eval_special_value(interp::JETInterpreter, @nospecialize(e), vtypes::VarTable, sv::InferenceState)
    toplevel = istoplevel(interp, sv)
    if toplevel
        if isa(e, Slot) && is_global_slot(interp, e)
            if get_slottype(sv, e) === Bottom
                # if this abstract global variable is not initialized, form the global
                # reference and abstract intepret it; we may have abstract interpreted this
                # variable and it may have a type
                # if it's really not defined, the error will be generated later anyway
                e = GlobalRef(interp.toplevelmod, get_slotname(sv, e))
            end
        elseif isa(e, Symbol)
            # (already concretized) toplevel global symbols
            e = GlobalRef(interp.toplevelmod, e)
        end
    end

    ret = @invoke abstract_eval_special_value(interp::AbstractInterpreter, e, vtypes::VarTable, sv::InferenceState)

    if isa(e, GlobalRef)
        mod, name = e.mod, e.name
        if isdefined(mod, name)
            if name === :Main
                # special case and propagate `Main` module as constant
                # XXX this was somewhat critical for accuracy and performance, but I'm not sure this still holds
                ret = Const(Main)
            elseif toplevel
                # here we will eagerly propagate the type of this global variable
                # of course the traced type might be difference from its type in actual execution
                # e.g. we don't track a global variable assignment wrapped in a function,
                # but it's highly possible this is a toplevel callsite and we need to take a
                # risk here, otherwise we can't enter the analysis !
                val = getfield(mod, name)
                ret = isa(val, AbstractGlobal) ? val.t : Const(val)
            else
                # TODO: add report pass to detect non-constant global variable here (for performance linting)
            end
        else
            # report pass for undefined global reference
            report_pass!(GlobalUndefVarErrorReport, interp, sv, mod, name)

            # `ret` at this point should be annotated as `Any` by `NativeInterpreter`, and we
            # just pass it as is to collect as much error points as possible within this frame
            # IDEA we can change it to `Bottom` to suppress any further abstract interpretation
            # with this variable, but at the same time we need to make sure we will invalidate
            # the cache for this frame on the future definition of this (currently) undefined binding
            # return Bottom
        end
    end

    return ret
end

function CC.abstract_eval_value(interp::JETInterpreter, @nospecialize(e), vtypes::VarTable, sv::InferenceState)
    ret = @invoke abstract_eval_value(interp::AbstractInterpreter, e, vtypes::VarTable, sv::InferenceState)

    # HACK if we encounter `_INACTIVE_EXCEPTION`, it means `ConcreteInterpreter` tried to
    # concretize an exception which was not actually thrown – yet the actual error hasn't
    # happened thanks to JuliaInterpreter's implementation detail, i.e. JuliaInterpreter
    # could retrieve `FrameData.last_exception`, which is initialized with
    # `_INACTIVE_EXCEPTION.instance` – but it's obviously not a sound approximation of an
    # actual execution and so here we will fix it to `Any`, since we don't analyze types of
    # exceptions in general
    if ret ⊑ _INACTIVE_EXCEPTION
        ret = Any
    end

    # report non-boolean condition error
    stmt = get_stmt(sv)
    if isa(stmt, GotoIfNot)
        t = widenconst(ret)
        if t !== Bottom
            report_pass!(NonBooleanCondErrorReport, interp, sv, t)
            # if this condition leads to an "non-boolean (t) used in boolean context" error,
            # we can turn it into Bottom and bail out early
            # TODO upstream this
            if typeintersect(Bool, t) !== Bool
                ret = Bottom
            end
        end
    end

    return ret
end

function CC.abstract_eval_statement(interp::JETInterpreter, @nospecialize(e), vtypes::VarTable, sv::InferenceState)
    if istoplevel(interp, sv)
        if interp.concretized[get_currpc(sv)]
            return Any # bail out if it has been interpreted by `ConcreteInterpreter`
        end
    end

    return @invoke abstract_eval_statement(interp::AbstractInterpreter, e, vtypes::VarTable, sv::InferenceState)
end

function CC.finish(me::InferenceState, interp::JETInterpreter)
    @invoke finish(me::InferenceState, interp::AbstractInterpreter)

    if istoplevel(interp, me)
        # find assignments of abstract global variables, and assign types to them,
        # so that later analysis can refer to them

        stmts = me.src.code
        cfg = compute_basic_blocks(stmts)
        assigns = Dict{Int,Bool}() # slot id => is this deterministic
        for (pc, stmt) in enumerate(stmts)
            if @isexpr(stmt, :(=))
                lhs = first(stmt.args)
                if isa(lhs, Slot)
                    slot = slot_id(lhs)
                    if is_global_slot(interp, slot)
                        isnd = is_assignment_nondeterministic(cfg, pc)

                        # COMBAK this approach is really not true when there're multiple
                        # assignments in different basic blocks
                        if haskey(assigns, slot)
                            assigns[slot] |= isnd
                        else
                            assigns[slot] = isnd
                        end
                    end
                end
            end
        end

        if !isempty(assigns)
            slottypes = collect_slottypes(me)
            for (slot, isnd) in assigns
                slotname = interp.global_slots[slot]
                typ = slottypes[slot]
                set_abstract_global!(interp, interp.toplevelmod, slotname, typ, isnd, me)
            end
        end
    end
end

# simple cfg analysis to check if the assignment at `pc` will happen non-deterministically
function is_assignment_nondeterministic(cfg::CFG, pc::Int)
    isnd = false

    blocks = cfg.blocks
    for (idx, block) in enumerate(blocks)
        if pc in rng(block)
            for block′ in blocks
                succs = block′.succs
                if idx in succs
                    isnd |= length(succs) > 1
                end
            end
        end
    end

    return isnd
end

# at this point all the types of SSA values are iterated to maximum fixed point,
# and we can compute types of slot as least upper bound of types of all the possible
# assignment of the slot (the type of assignment statement is available as SSA value type)
# the implementation is mostly same as `record_slot_assign!(sv::InferenceState)`, but
# we don't `widenconst` each SSA value type
function collect_slottypes(sv::InferenceState)
    states = sv.stmt_types
    ssavaluetypes = sv.src.ssavaluetypes::Vector{Any}
    stmts = sv.src.code::Vector{Any}
    slottypes = Any[Bottom for _ in sv.src.slottypes::Vector{Any}]
    for i = 1:length(stmts)
        stmt = stmts[i]
        state = states[i]
        # find all reachable assignments to locals
        if isa(state, VarTable) && @isexpr(stmt, :(=))
            lhs = first(stmt.args)
            if isa(lhs, Slot)
                vt = ssavaluetypes[i] # don't widen const
                if vt !== Bottom
                    id = slot_id(lhs)
                    otherTy = slottypes[id]
                    slottypes[id] = tmerge(otherTy, vt)
                end
            end
        end
    end
    return slottypes
end

function set_abstract_global!(interp::JETInterpreter, mod::Module, name::Symbol, @nospecialize(t), isnd::Bool, sv::InferenceState)
    prev_agv = nothing
    prev_t = nothing
    iscd = is_constant_declared(name, sv)

    # check if this global variable is already assigned previously
    if isdefined(mod, name)
        val = getfield(mod, name)
        if isa(val, AbstractGlobal)
            prev_t = val.t
            if val.iscd && (prev_t′ = widenconst(prev_t)) !== (t′ = widenconst(t))
                warn_invalid_const_global!(name)
                report_pass!(InvalidConstantRedefinition, interp, sv, mod, name, prev_t′, t′)
                return
            end
            prev_agv = val
        else
            prev_t = Core.Typeof(val)
            if isconst(mod, name)
                invalid = prev_t !== (t′ = widenconst(t))
                if invalid || !isa(t, Const)
                    warn_invalid_const_global!(name)
                    if invalid
                        report_pass!(InvalidConstantRedefinition, interp, sv, mod, name, prev_t, t′)
                    end
                    return
                end
                # otherwise, we can just redefine this constant, and Julia will warn it
                ex = iscd ? :(const $name = $(QuoteNode(t.val))) : :($name = $(QuoteNode(t.val)))
                return Core.eval(mod, ex)
            end
        end
    end

    isnew = isnothing(prev_t)

    # if this constant declaration is invalid, just report it and bail out
    if iscd && !isnew
        warn_invalid_const_global!(name)
        report_pass!(InvalidConstantDeclaration, interp, sv, mod, name)
        return
    end

    # if this assignment happens non-deterministically, we need to take the previous type into account
    if isnd
        if !isnew # if this assignment is an initialization, we just need to use `t`
            t = tmerge(prev_t, t)
        end
    else
        # if this assignment happens deterministically, and the assigned value is known to be
        # constant statically, let's concretize it for good reasons;
        # we will be able to use it in concrete interpretation and so this allows to define
        # structs with type aliases, etc.
        if isa(t, Const)
            if iscd
                @assert isnew # means, this is a valid constant declaration
                return Core.eval(mod, :(const $name = $(QuoteNode(t.val))))
            else
                # we've checked `mod.name` wasn't declared as constant previously
                return Core.eval(mod, :($name = $(QuoteNode(t.val))))
            end
        end
    end

    # okay, we will define new abstract global variable from here on
    if isa(prev_agv, AbstractGlobal)
        return Core.eval(mod, :(let name = $name::$AbstractGlobal
            name.t = $t
            name
        end))
    else
        return Core.eval(mod, :($name = $(AbstractGlobal(t, iscd))))
    end
end

warn_invalid_const_global!(name::Symbol) = @warn """
JET.jl can't update the definition of this constant declared global variable: `$name`
This may fail, cause incorrect analysis, or produce unexpected errors.
"""

function is_constant_declared(name::Symbol, sv::InferenceState)
    return any(sv.src.code) do @nospecialize(x)
        if @isexpr(x, :const)
            arg = first(x.args)
            # `transform_global_symbols!` replaces all the global symbols in this toplevel frame with `Slot`s
            if isa(arg, Slot)
                return get_slotname(sv, arg) === name
            end
        end
        return false
    end
end

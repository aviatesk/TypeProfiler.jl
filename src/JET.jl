@doc read(normpath(dirname(@__DIR__), "README.md"), String)
module JET

const CC = Core.Compiler

@static isdefined(CC, :AbstractInterpreter) || throw(ErrorException("JET.jl only works with Julia versions 1.6 and higher"))

# imports
# =======

# `JETInterpreter`
import .CC:
    # abstractinterpreterinterface.jl
    InferenceParams,
    OptimizationParams,
    get_world_counter,
    lock_mi_inference,
    unlock_mi_inference,
    add_remark!,
    may_optimize,
    may_compress,
    may_discard_trees,
    # jetcache.jl
    code_cache,
    # haskey,
    # get,
    # getindex,
    # setindex!,
    get_inference_cache,
    cache_lookup,
    # push!,
    # tfuncs.jl
    builtin_tfunction,
    return_type_tfunc,
    # abstractinterpretation.jl
    abstract_call_gf_by_type,
    abstract_call_method_with_const_args,
    abstract_call_method,
    abstract_eval_special_value,
    abstract_eval_value,
    abstract_eval_statement,
    # typeinfer.jl
    typeinf,
    _typeinf,
    finish,
    # optimize.jl
    OptimizationState,
    optimize

# `ConcreteInterpreter`
import JuliaInterpreter:
    # virtualprocess.jl
    step_expr!,
    evaluate_call_recurse!,
    handle_err

# usings
# ======
# TODO: really use `using` instead

import Core:
    Intrinsics,
    Builtin,
    MethodMatch,
    LineInfoNode,
    NewvarNode,
    SimpleVector,
    svec

import .CC:
    AbstractInterpreter,
    NativeInterpreter,
    InferenceState,
    InferenceResult,
    CodeInfo,
    InternalCodeCache,
    CodeInstance,
    WorldRange,
    WorldView,
    MethodInstance,
    Bottom,
    NOT_FOUND,
    MethodMatchInfo,
    UnionSplitInfo,
    MethodLookupResult,
    Const,
    VarState,
    VarTable,
    SSAValue,
    SlotNumber,
    Slot,
    slot_id,
    GlobalRef,
    GotoIfNot,
    ReturnNode,
    widenconst,
    ⊑,
    CallMeta,
    is_throw_call,
    tmerge,
    argtypes_to_type,
    argtype_by_index,
    argtype_tail,
    _methods_by_ftype,
    specialize_method,
    add_backedge!,
    add_mt_backedge!,
    compute_basic_blocks,
    matching_cache_argtypes,
    is_argtype_match,
    tuple_tfunc

import Base:
    parse_input_line,
    unwrap_unionall,
    rewrap_unionall,
    Fix1,
    Fix2,
    IdSet

import Base.Meta:
    _parse_string,
    lower

using LoweredCodeUtils, JuliaInterpreter

import LoweredCodeUtils:
    istypedef,
    ismethod,
    callee_matches

import JuliaInterpreter:
    bypass_builtins,
    maybe_evaluate_builtin,
    collect_args,
    is_return,
    is_quotenode_egal

using InteractiveUtils

# common
# ======

# hooks
# -----

const INIT_HOOKS = Function[]
push_inithook!(f) = push!(INIT_HOOKS, f)
__init__() = foreach(@nospecialize(f)->f(), INIT_HOOKS)

# compat
# ------

const BACKEDGE_CALLBACK_ENABLED = :callbacks in fieldnames(Core.MethodInstance)

@static BACKEDGE_CALLBACK_ENABLED || push_inithook!() do
@warn """with your Julia version, JET.jl may not be able to update analysis result
correctly after refinement of a method in deeper call sites
"""
end

@static if isdefined(CC, :LimitedAccuracy)
    import .CC: ignorelimited
else
    ignorelimited(@nospecialize(x)) = x
end

# macros
# ------

# to circumvent https://github.com/JuliaLang/julia/issues/37342, we inline these `isa`
# condition checks at surface AST level
macro isexpr(ex, args...)
    ex   = esc(ex)
    args = map(esc, args)
    return :($(GlobalRef(Core, :isa))($(ex), $(GlobalRef(Core, :Expr))) && $(_isexpr_check)($(ex), $(args...)))
end

_isexpr_check(ex::Expr, head::Symbol)         = ex.head === head
_isexpr_check(ex::Expr, heads)                = in(ex.head, heads)
_isexpr_check(ex::Expr, head::Symbol, n::Int) = ex.head === head && length(ex.args) == n
_isexpr_check(ex::Expr, heads, n::Int)        = in(ex.head, heads) && length(ex.args) == n

"""
    @invoke f(arg::T, ...; kwargs...)

Provides a convenient way to call [`invoke`](https://docs.julialang.org/en/v1/base/base/#Core.invoke);
`@invoke f(arg1::T1, arg2::T2; kwargs...)` will be expanded into `invoke(f, Tuple{T1,T2}, arg1, arg2; kwargs...)`.
When an argument's type annotation is omitted, it's specified as `Any` argument, e.g.
`@invoke f(arg1::T, arg2)` will be expanded into `invoke(f, Tuple{T,Any}, arg1, arg2)`.

This could be used to call down to `NativeInterpreter`'s abstract interpretation method of
  `f` while passing `JETInterpreter` so that subsequent calls of abstract interpretation
  functions overloaded against `JETInterpreter` can be called from the native method of `f`;
e.g. calls down to `NativeInterpreter`'s `abstract_call_gf_by_type` method:
```julia
@invoke abstract_call_gf_by_type(interp::AbstractInterpreter, f, argtypes::Vector{Any}, atype, sv::InferenceState,
                                 max_methods::Int)
```
"""
macro invoke(ex)
    f, args, kwargs = destructure_callex(ex)
    arg2typs = map(args) do x
        if @isexpr(x, :macrocall) && first(x.args) === Symbol("@nospecialize")
            x = last(x.args)
        end
        @isexpr(x, :(::)) ? (x.args...,) : (x, GlobalRef(Core, :Any))
    end
    args, argtypes = first.(arg2typs), last.(arg2typs)
    return esc(:($(GlobalRef(Core, :invoke))($(f), Tuple{$(argtypes...)}, $(args...); $(kwargs...))))
end

"""
    @invokelatest f(args...; kwargs...)

Provides a convenient way to call [`Base.invokelatest`](https://docs.julialang.org/en/v1/base/base/#Base.invokelatest).
`@invokelatest f(args...; kwargs...)` will simply be expanded into
`Base.invokelatest(f, args...; kwargs...)`.
"""
macro invokelatest(ex)
    f, args, kwargs = destructure_callex(ex)
    return esc(:($(GlobalRef(Base, :invokelatest))($(f), $(args...); $(kwargs...))))
end

function destructure_callex(ex)
    @assert @isexpr(ex, :call) "call expression f(args...; kwargs...) should be given"

    f = first(ex.args)
    args = []
    kwargs = []
    for x in ex.args[2:end]
        if @isexpr(x, :parameters)
            append!(kwargs, x.args)
        elseif @isexpr(x, :kw)
            push!(kwargs, x)
        else
            push!(args, x)
        end
    end

    return f, args, kwargs
end

"""
    @withmixedhash (mutable) struct T
        fields ...
    end

Defines struct `T` while automatically defining its `Base.hash(::T, ::UInt)` method which
  mixes hashes of all of `T`'s fields (and also corresponding `Base.:(==)(::T, ::T)` method).

This macro is supposed to abstract the following kind of pattern:

> https://github.com/aviatesk/julia/blob/999973df2850d6b2e0bd4bcf03ef90a14217b63c/base/pkgid.jl#L3-L25
```julia
struct PkgId
    uuid::Union{UUID,Nothing}
    name::String
end

==(a::PkgId, b::PkgId) = a.uuid == b.uuid && a.name == b.name

function hash(pkg::PkgId, h::UInt)
    h += 0xc9f248583a0ca36c % UInt
    h = hash(pkg.uuid, h)
    h = hash(pkg.name, h)
    return h
end
```

> with `@withmixedhash`
```julia
@withmixedhash struct PkgId
    uuid::Union{UUID,Nothing}
    name::String
end
```

See also: [`EGAL_TYPES`](@ref)
"""
macro withmixedhash(typedef)
    @assert @isexpr(typedef, :struct) "struct definition should be given"
    name = typedef.args[2]
    flddef = typedef.args[3]
    fld2typs = map(filter(!islnn, typedef.args[3].args)) do x
        if @isexpr(x, :(::))
            fld, typex = x.args
            typ = Core.eval(__module__, typex)
            fld, typ
        else
            (x, Any)
        end
    end
    @assert !isempty(fld2typs) "no fields given, nothing to hash"

    h_init = UInt === UInt64 ? rand(UInt64) : rand(UInt32)
    hash_body = quote h = $(h_init) end
    for (fld, typ) in fld2typs
        push!(hash_body.args, :(h = $(Base.hash)(x.$fld, h)))
    end
    push!(hash_body.args, :(return h))
    hash_func = :(function Base.hash(x::$name, h::UInt); $(hash_body); end)
    eq_body = foldr(fld2typs; init = true) do (fld, typ), x
        eq_ex = if all(in(EGAL_TYPES), typenames(typ))
            :(x1.$fld === x2.$fld)
        else
            :(x1.$fld == x2.$fld)
        end
        Expr(:&&, eq_ex, x)
    end
    eq_func = :(function Base.:(==)(x1::$name, x2::$name); $(eq_body); end)

    return quote
        $(typedef)
        $(hash_func)
        $(eq_func)
    end
end

islnn(@nospecialize(_)) = false
islnn(::LineNumberNode) = true

"""
    const EGAL_TYPES = $(EGAL_TYPES)

Keeps names of types that should be compared by `===` rather than `==`.

See also: [`@withmixedhash`](@ref)
"""
const EGAL_TYPES = Set{Symbol}((:Type, :Symbol, :MethodInstance))

typenames(@nospecialize(t::DataType)) = [t.name.name]
typenames(u::Union)                   = collect(Base.Iterators.flatten(typenames.(CC.uniontypes(u))))
typenames(u::UnionAll)                = [u.body.name.name]

"""
    @jetconfigurable function config_func(args...; configurations...)
        ...
    end

This macro asserts that there's no configuration naming conflict across the `@jetconfigurable`
  functions so that a configuration for a `@jetconfigurable` function  doesn't affect the other
  `@jetconfigurable` functions.
This macro also adds a dummy splat keyword arguments (`jetconfigs...`) to the function definition
  so that any configuration of other `@jetconfigurable` functions can be passed on to it.
"""
macro jetconfigurable(funcdef)
    @assert @isexpr(funcdef, :(=)) || @isexpr(funcdef, :function) "function definition should be given"

    defsig = funcdef.args[1]
    thisname = first(defsig.args)
    i = findfirst(a->@isexpr(a, :parameters), defsig.args)
    if isnothing(i)
        @warn "no JET configurations are defined for `$thisname`"
        insert!(defsig.args, 2, Expr(:parameters, :(jetconfigs...)))
    else
        kwargs = defsig.args[i]
        found = false
        for kwarg in kwargs.args
            if @isexpr(kwarg, :...)
                found = true
                continue
            end
            kwargex = first(kwarg.args)
            kwargname = (@isexpr(kwargex, :(::)) ? first(kwargex.args) : kwargex)::Symbol
            othername = get!(_JET_CONFIGURATIONS, kwargname, thisname)
            # allows same configurations for same generic function or function refinement
            @assert thisname === othername "`$thisname` uses `$kwargname` JET configuration name which is already used by `$othername`"
        end
        found || push!(kwargs.args, :(jetconfigs...))
    end

    return esc(funcdef)
end
const _JET_CONFIGURATIONS = Dict{Symbol,Symbol}()

# utils
# -----

function is_constant_propagated(frame::InferenceState)
    return !frame.cached && CC.any(frame.result.overridden_by_const)
end

@inline istoplevel(linfo::MethodInstance) = linfo.def === __virtual_toplevel__
@inline istoplevel(sv::InferenceState)    = istoplevel(sv.linfo)

prewalk_inf_frame(@nospecialize(f), ::Nothing) = return
function prewalk_inf_frame(@nospecialize(f), frame::InferenceState)
    ret = f(frame)
    prewalk_inf_frame(f, frame.parent)
    return ret
end

postwalk_inf_frame(@nospecialize(f), ::Nothing) = return
function postwalk_inf_frame(@nospecialize(f), frame::InferenceState)
    postwalk_inf_frame(f, frame.parent)
    return f(frame)
end

# NOTE: these methods are supposed to be called while abstract interpretaion
# and as such aren't valid after finishing it (i.e. optimization, etc.)
@inline get_currpc(frame::InferenceState)                          = min(frame.currpc, length(frame.src.code))
@inline get_stmt(frame::InferenceState, pc = get_currpc(frame))    = @inbounds frame.src.code[pc]
@inline get_states(frame::InferenceState, pc = get_currpc(frame))  = @inbounds frame.stmt_types[pc]::VarTable
@inline get_codeloc(frame::InferenceState, pc = get_currpc(frame)) = @inbounds frame.src.codelocs[pc]
@inline get_lin(frame::InferenceState, loc = get_codeloc(frame))   = @inbounds (frame.src.linetable::Vector)[loc]::LineInfoNode

@inline get_slotname(frame::InferenceState, slot::Int)             = @inbounds frame.src.slotnames[slot]
@inline get_slotname(frame::InferenceState, slot::Slot)            = get_slotname(frame, slot_id(slot))
@inline get_slottype(frame::InferenceState, slot::Int)             = @inbounds (get_states(frame)[slot]::VarState).typ
@inline get_slottype(frame::InferenceState, slot::Slot)            = get_slottype(frame, slot_id(slot))

@inline get_result(frame::InferenceState)                          = frame.bestguess

ignorenotfound(@nospecialize(t)) = t === NOT_FOUND ? Bottom : t

# includes
# ========

include("reports.jl")
include("abstractinterpreterinterface.jl")
include("jetcache.jl")
include("tfuncs.jl")
include("abstractinterpretation.jl")
include("typeinfer.jl")
include("optimize.jl")
include("print.jl")
include("virtualprocess.jl")
include("watch.jl")

# entry
# =====

"""
    report_file([io::IO = stdout],
                filename::AbstractString,
                mod::Module = Main;
                jetconfigs...) -> included_files::Set{String}, any_reported::Bool

Reads a text of `filename` and then calls [`report_text`](@ref) on it.
"""
function report_file(io::IO,
                     filename::AbstractString,
                     mod::Module = Main;
                     jetconfigs...)
    text = read(filename, String)
    return report_text(io, text, filename, mod; jetconfigs...)
end
report_file(args...; jetconfigs...) = report_file(stdout::IO, args...; jetconfigs...)

"""
    report_text([io::IO = stdout],
                text::AbstractString,
                filename::AbstractString = "top-level",
                mod::Module = Main;
                jetconfigs...) -> included_files::Set{String}, any_reported::Bool

Analyzes `text`, prints the collected error reports to the `io` stream, and finally returns:
- `included_files::Set{String}`: files analyzed by JET
- `any_reported`: indicates if there was any error point reported

`filename` is supposed to be the name of file, whose content is `text`, and `mod` will
  specify the module context of toplevel execution simulation.
"""
function report_text(io::IO,
                     text::AbstractString,
                     filename::AbstractString = "top-level",
                     mod::Module = Main;
                     jetconfigs...)
    included_files, reports, postprocess = collect_reports(mod,
                                                           text,
                                                           filename;
                                                           jetconfigs...)
    return included_files, print_reports(io, reports, postprocess; jetconfigs...)
end
report_text(args...; jetconfigs...) = report_text(stdout::IO, args...; jetconfigs...)

function collect_reports(actualmod, text, filename; jetconfigs...)
    interp = JETInterpreter(; jetconfigs...)

    virtualmod = gen_virtual_module(actualmod)
    res = virtual_process!(text,
                           filename,
                           virtualmod,
                           Symbol(actualmod),
                           interp,
                           )

    return res.included_files,
           # non-empty `ret.toplevel_error_reports` means critical errors happened during
           # the AST transformation, so they always have precedence over `ret.inference_error_reports`
           !isempty(res.toplevel_error_reports) ? res.toplevel_error_reports : res.inference_error_reports,
           gen_postprocess(virtualmod, actualmod)
end

gen_virtual_module(actualmod = Main) =
    return Core.eval(actualmod, :(module $(gensym(:JETVirtualModule)) end))::Module

# fix virtual module printing based on string manipulation; the "actual" modules may not be
# loaded into this process
function gen_postprocess(virtualmod, actualmod)
    virtual = string(virtualmod)
    actual  = string(actualmod)
    return actualmod == Main ?
           Fix2(replace, "Main." => "") ∘ Fix2(replace, virtual => actual) :
           Fix2(replace, virtual => actual)
end

# this dummy module will be used by `istoplevel` to check if the current inference frame is
# created by `analyze_toplevel!` or not (i.e. `@generated` function)
module __virtual_toplevel__ end

function analyze_toplevel!(interp::JETInterpreter, src::CodeInfo)
    # construct toplevel `MethodInstance`
    mi = ccall(:jl_new_method_instance_uninit, Ref{Core.MethodInstance}, ());
    mi.uninferred = src
    mi.specTypes = Tuple{}

    transform_abstract_global_symbols!(interp, src)
    mi.def = __virtual_toplevel__ # set to the dummy module

    result = InferenceResult(mi);
    # toplevel frame doesn't need to be cached (and so it won't be optimized)
    frame = InferenceState(result, src, #=cached=# false, interp)::InferenceState;

    return analyze_frame!(interp, frame)
end

# HACK this is an native hack to re-use `AbstractInterpreter`'s approximated slot types for
# assignment of abstract global variable, which are represented as toplevel symbols at this point;
# the idea is just transform them into slots and use their approximated type for their
# abstract global assignment.
# NOTE that transformations by `transform_abstract_global_symbols!` will produce really
# invalid code for interpreting transformed statments, but all the statements won't be
# actually executed nor interpreted by `ConcreteInterpreter`
function transform_abstract_global_symbols!(interp::JETInterpreter, src::CodeInfo)
    nslots = length(src.slotnames)
    abstrct_global_variables = Dict{Symbol,Int}()
    concretized = interp.concretized

    # linear scan, and find assignments of abstract global variables
    for (i, stmt) in enumerate(src.code::Vector{Any})
        if @isexpr(stmt, :(=))
            lhs = first(stmt.args)
            if isa(lhs, Symbol)
                if !(concretized[i])
                    if !haskey(abstrct_global_variables, lhs)
                        nslots += 1
                        push!(abstrct_global_variables, lhs => nslots)
                    end
                end
            end
        end
    end

    function _transform_abstract_global_symbols!(x, scope)
        if isa(x, Symbol)
            slot = get(abstrct_global_variables, x, nothing)
            if !isnothing(slot)
                return SlotNumber(slot)
            end
        elseif isa(x, GotoIfNot)
            newcond = _transform_abstract_global_symbols!(x.cond, scope)
            return GotoIfNot(newcond, x.dest)
        end

        return x
    end
    prewalk_and_transform!(_transform_abstract_global_symbols!, src)

    resize!(src.slotnames, nslots)
    resize!(src.slotflags, nslots)
    for (slotname, idx) in abstrct_global_variables
        src.slotnames[idx] = slotname
    end

    interp.global_slots = Dict(idx => slotname for (slotname, idx) in abstrct_global_variables)
end

# TODO `analyze_call_builtin!` ?
function analyze_gf_by_type!(interp::JETInterpreter, @nospecialize(tt::Type{<:Tuple}))
    mm = get_single_method_match(tt, InferenceParams(interp).MAX_METHODS, get_world_counter(interp))
    return analyze_method_signature!(interp, mm.method, mm.spec_types, mm.sparams)
end

function get_single_method_match(@nospecialize(tt), lim, world)
    mms = _methods_by_ftype(tt, lim, world)
    @assert !isa(mms, Bool) "unable to find matching method for $(tt)"

    filter!(mm::MethodMatch->mm.spec_types===tt, mms)
    @assert length(mms) == 1 "unable to find single target method for $(tt)"

    return first(mms)::MethodMatch
end

analyze_method!(interp::JETInterpreter, m::Method) =
    analyze_method_signature!(interp, m, m.sig, method_sparams(m))

function method_sparams(m::Method)
    s = TypeVar[]
    sig = m.sig
    while isa(sig, UnionAll)
        push!(s, sig.var)
        sig = sig.body
    end
    return svec(s...)
end

function analyze_method_signature!(interp::JETInterpreter,
                                   m::Method,
                                   @nospecialize(atype),
                                   sparams::SimpleVector,
                                   )
    mi = specialize_method(m, atype, sparams)

    result = InferenceResult(mi)

    frame = InferenceState(result, #=cached=# true, interp)::InferenceState

    return analyze_frame!(interp, frame)
end

function analyze_frame!(interp::JETInterpreter, frame::InferenceState)
    typeinf(interp, frame)

    # report `throw` calls "appropriately";
    # if the final return type here is `Bottom`-annotated, it _may_ mean the control flow
    # didn't catch some of the `UncaughtExceptionReport`s stashed within `interp.uncaught_exceptions`,
    if get_result(frame) === Bottom
        if !isempty(interp.uncaught_exceptions)
            append!(interp.reports, interp.uncaught_exceptions)
        end
    end

    return interp, frame
end

# test, interactive
# =================

"""
    @analyze_call [jetconfigs...] f(args...)

Evaluates the arguments to the function call, determines its types, and then calls
  [`analyze_call`](@ref) on the resulting expression.
As with `@code_typed` and its family, any of [JET configurations](@ref) can be given as the optional
  arguments like this:
```julia
# analyzes `rand(::Type{Bool})` with `aggressive_constant_propagation` configuration turned off
julia> @analyze_call aggressive_constant_propagation=false rand(Bool)
```
"""
macro analyze_call(ex0...)
    return InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :analyze_call, ex0)
end

"""
    analyze_call(f, types = Tuple{}; jetconfigs...) -> (interp::JETInterpreter, frame::InferenceFrame)

Analyzes the generic function call with the given type signature, and returns:
- `interp::JETInterpreter`, which contains analyzed error reports and such
- `frame::InferenceFrame`, which is the final state of the abstract interpretation
"""
function analyze_call(@nospecialize(f), @nospecialize(types = Tuple{}); jetconfigs...)
    ft = Core.Typeof(f)
    if isa(types, Type)
        u = unwrap_unionall(types)
        tt = rewrap_unionall(Tuple{ft, u.parameters...}, types)
    else
        tt = Tuple{ft, types...}
    end

    interp = JETInterpreter(; jetconfigs...)
    return analyze_gf_by_type!(interp, tt)
end

"""
    @report_call [jetconfigs...] f(args...)

Evaluates the arguments to the function call, determines its types, and then calls
  [`report_call`](@ref) on the resulting expression.
As with `@code_typed` and its family, any of [JET configurations](@ref) can be given as the optional
  arguments like this:
```julia
# reports `rand(::Type{Bool})` with `aggressive_constant_propagation` configuration turned off
julia> @report_call aggressive_constant_propagation=false rand(Bool)
```
"""
macro report_call(ex0...)
    return InteractiveUtils.gen_call_with_extracted_types_and_kwargs(__module__, :report_call, ex0)
end

"""
    report_call(f, types = Tuple{}; jetconfigs...) -> result_type::Any

Analyzes the generic function call with the given type signature, and then prints collected
  error points to `stdout`, and finally returns the result type of the call.
"""
function report_call(@nospecialize(f), @nospecialize(types = Tuple{}); jetconfigs...)
    interp, frame = analyze_call(f, types; jetconfigs...)
    print_reports(interp.reports; jetconfigs...)
    return get_result(frame)
end

print_reports(args...; jetconfigs...) = print_reports(stdout::IO, args...; jetconfigs...)

# for inspection
macro lwr(ex) QuoteNode(lower(__module__, ex)) end
macro src(ex) QuoteNode(first(lower(__module__, ex).args)) end

# exports
# =======

export
    report_file,
    report_and_watch_file,
    report_text,
    @analyze_call,
    analyze_call,
    @report_call,
    report_call

end

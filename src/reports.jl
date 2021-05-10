# toplevel
# ========

"""
    ToplevelErrorReport

An interface type of error reports that JET collects while top-level concrete interpration.
All `ToplevelErrorReport` should have the following fields:
- `file::String`: the path to the file containing the interpretation context
- `line::Int`: the line number in the file containing the interpretation context

See also: [`virtual_process`](@ref), [`ConcreteInterpreter`](@ref)
"""
abstract type ToplevelErrorReport end

# `ToplevelErrorReport` interface
function Base.getproperty(er::ToplevelErrorReport, sym::Symbol)
    return if sym === :file
        getfield(er, sym)::String
    elseif sym === :line
        getfield(er, sym)::Int
    else
        getfield(er, sym) # fallback
    end
end

struct SyntaxErrorReport <: ToplevelErrorReport
    err::ErrorException
    file::String
    line::Int
    SyntaxErrorReport(msg::AbstractString, file, line) = new(ErrorException(msg), file, line)
end

struct RecursiveIncludeErrorReport <: ToplevelErrorReport
    duplicated_file::String
    files::Set{String}
    file::String
    line::Int
end

# wraps general errors from actual execution
struct ActualErrorWrapped <: ToplevelErrorReport
    err
    st::Base.StackTraces.StackTrace
    file::String
    line::Int

    # default constructor
    ActualErrorWrapped(err, st, file, line) = new(err, st, file, line)

    # bypass syntax error
    function ActualErrorWrapped(err::ErrorException, st, file, line)
        return if startswith(err.msg, "syntax: ")
            SyntaxErrorReport(err.msg, file, line)
        else
            new(err, st, file, line)
        end
    end
end

# wraps an error that might happen because of inappropriate top-level code abstraction
struct MissingConcretization <: ToplevelErrorReport
    err
    st::Base.StackTraces.StackTrace
    file::String
    line::Int
end

# inference
# =========

"""
    VirtualFrame

Stack information representing virtual execution context:
- `file::Symbol`: the path to the file containing the virtual execution context
- `line::Int`: the line number in the file containing the virtual execution context
- `sig::Vector{Any}`: a signature of this frame
- `linfo::MethodInstance`: The `MethodInstance` containing the execution context

This type is very similar to `Base.StackTraces.StackFrame`, but its execution context is
collected during abstract interpration, not collected from actual execution.
"""
@withmixedhash struct VirtualFrame
    file::Symbol
    line::Int
    sig::Vector{Any}
    linfo::MethodInstance
end

"""
    VirtualStackTrace

Represents a virtual stack trace in the form of a vector of `VirtualFrame`.
The vector holds `VirtualFrame`s in order of "from entry call site to error point", i.e.
the first element is the `VirtualFrame` of the entry call site, and the last element is that
contains the error.
"""
const VirtualStackTrace = Vector{VirtualFrame}

const INFERENCE_ERROR_REPORT_FIELD_DECLS = [
    :(vst::VirtualStackTrace),
    :(msg::String),
    :(sig::Vector{Any}),
]

"""
    InferenceErrorReport

An interface type of error reports that JET collects by abstract interpration.
If `T` implements this interface, the following requirements should be satisfied:

---
- **Required fields** \\
  `T` should have the following fields, which explains _where_ and _why_ this error is reported:
  * `vst::VirtualStackTrace`: a virtual stack trace of the error
  * `msg::String`: explains why this error is reported
  * `sig::Vector{Any}`: a signature of the error point

  Note that `T` can still have additional fields specific to it.
---
- **A constructor interface to create `T` from abstraction interpretation** \\
  `T<:InferenceErrorReport` has the default constructor

      T(::JETInterpreter, sv::InferenceState, spec_args...)

  which works when `T` is reported when `sv`'s program counter (`sv.currpc`) points to that
  of statement where the error may happen. If so `T` just needs to overload

      get_msg(::Type{T}, ::JETInterpreter, ::InferenceState, spec_args...) -> msg::String

  to provide the message that describes why this error is reported (otherwise the senseless
  default message will be used).

  ---

  If `T` is reported when `sv`'s program counter (`sv.currpc`) may not point to the error
  location or even `sv::InferenceState` isn't available, `T` can implement its own constructor method.
---
- **A contructor interface to create `T` from the global report cache** \\
  In order to be cached and restored from [`JET_REPORT_CACHE`](@ref), `T` _**must**_ implement
  the following interfaces:
  * `spec_args(::T) -> Tuple{...}`:
    returns fields that are specific to `T`, which is internally used by the caching logic
  * `T(vst::VirtualStackTrace, msg::String, sig::Vector{Any} spec_args::Tuple{...}) -> T`:
    constructor to create `T` from the cache, which should expand `spec_args` into each specific field
---

To satisfy these requirements manually will be very tedious.
JET internally uses `@reportdef` utility macro, which takes the `struct` definition of
`InferenceErrorReport` and automatically defines the `struct` itself and the cache interfaces.

See also: [`VirtualStackTrace`](@ref), [`VirtualFrame`](@ref)
"""
abstract type InferenceErrorReport end

# to help inference
function Base.getproperty(er::InferenceErrorReport, sym::Symbol)
    return if sym === :vst
        getfield(er, sym)::VirtualStackTrace
    elseif sym === :msg
        getfield(er, sym)::String
    elseif sym === :sig
        getfield(er, sym)::Vector{Any}
    elseif sym === :lin # only needed for ExceptionReport
        getfield(er, sym)::LineInfoNode
    else
        getfield(er, sym) # fallback
    end
end

function Base.show(io::IO, report::T) where {T<:InferenceErrorReport}
    print(io, T.name.name, '(')
    for a in report.sig
        _print_signature(io, a, (; annotate_types = true); bold = true)
    end
    print(io, ')')
end
Base.show(io::IO, ::MIME"application/prs.juno.inline", report::T) where {T<:InferenceErrorReport} =
    return report

# default constructor to create a report from abstract interpretation routine
function (T::Type{<:InferenceErrorReport})(interp, sv::InferenceState, @nospecialize(spec_args...))
    vf = get_virtual_frame(interp, sv)
    msg = get_msg(T, interp, sv, spec_args...)
    return T([vf], msg, vf.sig, spec_args...)
end
get_msg(::Type{<:InferenceErrorReport}, interp, sv::InferenceState, @nospecialize(spec_args...)) = "FIXME (report message isn't implemented)"

# virtual frame
# -------------

function get_virtual_frame(interp, loc::Union{InferenceState,MethodInstance})
    sig = get_sig(interp, loc)
    file, line = get_file_line(loc)
    linfo = isa(loc, InferenceState) ? loc.linfo : loc
    return VirtualFrame(file, line, sig, linfo)
end

function get_virtual_frame(interp, sv::InferenceState, pc::Int)
    sig = get_sig(interp, sv, get_stmt(sv, pc))
    file, line = get_file_line(get_lin(sv, get_codeloc(sv, pc)))
    linfo = sv.linfo
    return VirtualFrame(file, line, sig, linfo)
end

get_file_line(frame::InferenceState) = get_file_line(get_lin(frame))
get_file_line(linfo::LineInfoNode)   = linfo.file, linfo.line
# this location is not exact, but this is whay we know at best
function get_file_line(linfo::MethodInstance)
    def = linfo.def

    isa(def, Method) && return def.file, Int(def.line)

    # top-level
    src = linfo.uninferred::CodeInfo
    return get_file_line(first(src.linetable::Vector)::LineInfoNode)
end

# signature
# ---------

# adapted from https://github.com/JuliaLang/julia/blob/0f11a7bb07d2d0d8413da05dadd47441705bf0dd/base/show.jl#L989-L1011
function get_sig(interp, l::MethodInstance)
    def = l.def
    ret = if isa(def, Method)
        if isdefined(def, :generator) && l === def.generator
            # print(io, "MethodInstance generator for ")
            # show(io, def)
            sprint(show, def)
        else
            # print(io, "MethodInstance for ")
            sprint(show_tuple_as_call, def.name, l.specTypes)
        end
    else
        # print(io, "Toplevel MethodInstance thunk")
        # # `thunk` is not very much information to go on. If this
        # # MethodInstance is part of a stacktrace, it gets location info
        # # added by other means.  But if it isn't, then we should try
        # # to print a little more identifying information.
        # if !from_stackframe
        #     linetable = l.uninferred.linetable
        #     line = isempty(linetable) ? "unknown" : (lt = linetable[1]; string(lt.file) * ':' * string(lt.line))
        #     print(io, " from ", def, " starting at ", line)
        # end
        "toplevel"
    end
    return Any[ret]
end

@inline function show_tuple_as_call(io::IO, name::Symbol, @nospecialize(sig::Type))
    @static if hasmethod(Base.show_tuple_as_call, (IO, Symbol, Type), (:demangle, :kwargs, :argnames, :qualified))
        Base.show_tuple_as_call(io, name, sig; qualified = true)
    else
        Base.show_tuple_as_call(io, name, sig, false, nothing, nothing, true)
    end
end

get_sig(interp, sv::InferenceState, @nospecialize(x = get_stmt(sv))) = _get_sig(interp, sv, x)

_get_sig(args...) = first(_get_sig_type(args...))::Vector{Any}

function _get_callsig(interp, sv::InferenceState, @nospecialize(f), args::Vector{Any};
                      splat::Bool = false)
    sig = _get_sig(interp, sv, f)
    push!(sig, '(')

    nargs = length(args)
    for (i, arg) in enumerate(args)
        arg_sig = _get_sig(interp, sv, arg)
        append!(sig, arg_sig)
        if i ≠ nargs
            push!(sig, ", ")
        else
            splat && push!(sig, "...")
        end
    end
    push!(sig, ')')

    return sig
end

function _get_sig_type(interp, sv::InferenceState, expr::Expr)
    head = expr.head
    if head === :call
        f = first(expr.args)
        args = expr.args[2:end]

        # special case splat call signature
        if isa(f, GlobalRef) && f.name === :_apply_iterate && begin
                itf = first(args)
                isa(itf, GlobalRef) && itf.name === :iterate
            end
            f = args[2]
            args = args[3:end]
            return _get_callsig(interp, sv, f, args; splat = true), nothing
        else
            return _get_callsig(interp, sv, f, args), nothing
        end
    elseif head === :invoke
        f = expr.args[2]
        args = expr.args[3:end]
        return _get_callsig(interp, sv, f, args), nothing
    elseif head === :(=)
        return _get_sig_type(interp, sv, last(expr.args))
    elseif head === :static_parameter
        typ = widenconst(sv.sptypes[first(expr.args)])
        return Any['_', typ], typ
    else
        return Any[string(expr)], nothing
    end
end
function _get_sig_type(interp, sv::InferenceState, ssa::SSAValue)
    sig, sig_typ = _get_sig_type(interp, sv, sv.src.code[ssa.id])
    typ = widenconst(ignorelimited(ignorenotfound(sv.src.ssavaluetypes[ssa.id])))
    sig_typ == typ || push!(sig, typ)
    return sig, typ
end
function _get_sig_type(interp, sv::InferenceState, slot::SlotNumber)
    name = get_slotname(sv, slot)
    sig = string(name)
    if isempty(sig)
        sig = string(slot) # fallback if no explicit slotname
    end
    if istoplevel(interp, sv)
        # this is a abstract global variable, form the global reference
        return _get_sig_type(interp, sv, GlobalRef(interp.toplevelmod, name))
    else
        typ = widenconst(ignorelimited(get_slottype(sv, slot)))
        return Any[sig, typ], typ
    end
end
# NOTE `Argument` only appears after optimization
# and so we don't need to handle abstract global variable here, etc.
function _get_sig_type(interp, sv::InferenceState, arg::Argument)
    name = get_slotname(sv, arg.n)
    sig = string(name)
    typ = widenconst(ignorelimited(sv.slottypes[arg.n])) # NOTE after optimization, and so we can't use `get_slottype` here
    return Any[sig, typ], typ
end
_get_sig_type(interp, ::InferenceState, gr::GlobalRef) = Any[string(gr.mod, '.', gr.name)], nothing
function _get_sig_type(interp, sv::InferenceState, s::Symbol)
    if istoplevel(interp, sv)
        # this is concrete global variable, form the global reference
        return _get_sig_type(interp, sv, GlobalRef(interp.toplevelmod, s))
    else
        return Any[repr(s; context = :compact => true)], nothing
    end
end
function _get_sig_type(interp, sv::InferenceState, gotoifnot::GotoIfNot)
    sig  = Any[string("goto %", gotoifnot.dest, " if not "), _get_sig(interp, sv, gotoifnot.cond)...]
    return sig, nothing
end
function _get_sig_type(interp, sv::InferenceState, rn::ReturnNode)
    sig = is_unreachable(rn) ? Any["unreachable"] : Any["return ", _get_sig(interp, sv, rn.val)...]
    return sig, nothing
end
function _get_sig_type(interp, ::InferenceState, qn::QuoteNode)
    typ = typeof(qn.value)
    return Any[string(qn), typ], typ
end
_get_sig_type(interp, ::InferenceState, @nospecialize(x)) = Any[repr(x; context = :compact => true)], nothing

# cache
# -----

@eval struct InferenceErrorReportCache
    T::Type{<:InferenceErrorReport}
    $(INFERENCE_ERROR_REPORT_FIELD_DECLS...)
    spec_args::NTuple{N,Any} where N
end

function cache_report!(cache, report::T) where {T<:InferenceErrorReport}
    vst = copy(report.vst)
    new = InferenceErrorReportCache(T, vst, report.msg, report.sig, spec_args(report))
    return push!(cache, new)
end

function restore_cached_report!(cache::InferenceErrorReportCache, sv::InferenceState)
    report = restore_cached_report(cache)
    if isa(report, UncaughtExceptionReport)
        stash_uncaught_exception!(sv, report)
    else
        report!(sv, report)
    end
    return report
end

restore_cached_report(cache::InferenceErrorReportCache) =
    cache.T(copy(cache.vst), cache.msg, cache.sig, cache.spec_args)::InferenceErrorReport

# utility
# -------

# a simple utility macro to define `InferenceErrorReport` w/o code duplications
macro reportdef(ex)
    @assert @capture(ex, struct T_ <: S_; spec_sigs__; end)
    @assert Core.eval(__module__, S) <: InferenceErrorReport

    spec_decls = map(spec_sigs) do x
        if @isexpr(x, :macrocall) && x.args[1] === Symbol("@nospecialize")
            return x.args[3]
        end
        return x
    end
    spec_names = extract_decl_name.(spec_decls)
    spec_types = extract_decl_type.(spec_decls)

    T = esc(T)
    spec_args = esc(:spec_args)

    # cache constructor
    cache_constructor_sig = :($T(vst::VirtualStackTrace,
                                 msg::String,
                                 sig::Vector{Any},
                                 @nospecialize(spec_args::Tuple),
                                 ))
    cache_constructor_call = :($T(vst, msg, sig))
    for (i, spec_type) in enumerate(spec_types)
        push!(cache_constructor_call.args, :($spec_args[$i]::$spec_type))
    end
    cache_constructor = Expr(:function, cache_constructor_sig, Expr(:block, __source__,
        :(return @inbounds $cache_constructor_call),
    ))

    # cache helper
    spec_getter_sig = :($spec_args(report::$T))
    spec_getter_tuple = Expr(:tuple)
    for spec_name in spec_names
        getter = Expr(:call, GlobalRef(Base, :getproperty), :report, QuoteNode(spec_name))
        push!(spec_getter_tuple.args, getter)
    end
    spec_getter = Expr(:function, spec_getter_sig, Expr(:block, __source__,
        :(return $spec_getter_tuple::Tuple{$(spec_types...)}),
    ))

    return quote
        Base.@__doc__ struct $T <: $S
            $(INFERENCE_ERROR_REPORT_FIELD_DECLS...)
            $(spec_decls...)
            # esc is needed here since signanture might be `@nospecialize`d
            function $T($(INFERENCE_ERROR_REPORT_FIELD_DECLS...), $(map(esc, spec_sigs)...))
                new($(extract_decl_name.(INFERENCE_ERROR_REPORT_FIELD_DECLS)...), $(map(esc, spec_names)...))
            end
        end

        $cache_constructor

        $spec_getter
    end
end

extract_decl_name(@nospecialize(x)) = (@isexpr(x, :(::)) ? first(x.args) : x)::Symbol
extract_decl_type(@nospecialize(x)) = @isexpr(x, :(::)) ? last(x.args) : GlobalRef(Core, :Any)

# report, message
# ---------------

@reportdef struct NoMethodErrorReport <: InferenceErrorReport
    @nospecialize(t::Union{Type,Vector{Type}})
end
# TODO count invalid unon split case
get_msg(::Type{NoMethodErrorReport}, interp, sv::InferenceState, @nospecialize(t::Type)) =
    "no matching method found for call signature ($t)"
get_msg(::Type{NoMethodErrorReport}, interp, sv::InferenceState, ts::Vector{Type}) =
    "for $(length(ts)) of union split cases, no matching method found for call signatures ($(join(ts, ", "))))"

@reportdef struct InvalidBuiltinCallErrorReport <: InferenceErrorReport
    argtypes::Vector{Any}
end
get_msg(::Type{InvalidBuiltinCallErrorReport}, interp, sv::InferenceState, @nospecialize(args...)) =
    "invalid builtin function call"

@reportdef struct NoFieldErrorReport <: InferenceErrorReport
    @nospecialize(typ::Type)
    name::Symbol
end
get_msg(::Type{NoFieldErrorReport}, interp, sv::InferenceState, @nospecialize(typ::Type), name::Symbol) =
    "type $(typ) has no field $(name)"

@reportdef struct GlobalUndefVarErrorReport <: InferenceErrorReport
    mod::Module
    name::Symbol
end
get_msg(::Type{GlobalUndefVarErrorReport}, interp, sv::InferenceState, mod::Module, name::Symbol) =
    "variable $(mod).$(name) is not defined"

@reportdef struct LocalUndefVarErrorReport <: InferenceErrorReport
    name::Symbol
end
# use program counter where local undefined variable is found
function LocalUndefVarErrorReport(interp, sv::InferenceState, name::Symbol, pc::Int)
    vf = get_virtual_frame(interp, sv, pc)
    msg = "local variable $(name) is not defined"
    return LocalUndefVarErrorReport([vf], msg, vf.sig, name)
end

@reportdef struct NonBooleanCondErrorReport <: InferenceErrorReport
    @nospecialize(t::Union{Type,Vector{Type}})
end
get_msg(::Type{NonBooleanCondErrorReport}, interp, sv::InferenceState, @nospecialize(t::Type)) =
    "non-boolean ($t) used in boolean context"
get_msg(::Type{NonBooleanCondErrorReport}, interp, sv::InferenceState, ts::Vector{Type}) =
    "for $(length(ts)) of union split cases, non-boolean ($(join(ts, ", "))) used in boolean context"

@reportdef struct DivideErrorReport <: InferenceErrorReport end
let s = sprint(showerror, DivideError())
    global get_msg(::Type{DivideErrorReport}, interp, sv::InferenceState) = s
end

# TODO we may want to hoist `InvalidConstXXX` errors into top-level errors

@reportdef struct InvalidConstantRedefinition <: InferenceErrorReport
    mod::Module
    name::Symbol
    @nospecialize(t′::Any)
    @nospecialize(t::Any)
end
get_msg(::Type{InvalidConstantRedefinition}, interp, sv::InferenceState, mod::Module, name::Symbol, @nospecialize(t′::Any), @nospecialize(t::Any)) =
    "invalid redefinition of constant $(mod).$(name) (from $(t′) to $(t))"

@reportdef struct InvalidConstantDeclaration <: InferenceErrorReport
    mod::Module
    name::Symbol
end
get_msg(::Type{InvalidConstantDeclaration}, interp, sv::InferenceState, mod::Module, name::Symbol) =
    "cannot declare a constant $(mod).$(name); it already has a value"

@reportdef struct GeneratorErrorReport <: InferenceErrorReport
    err # actual error wrapped
end
function GeneratorErrorReport(interp, linfo::MethodInstance, err)
    vst = VirtualFrame[get_virtual_frame(interp, linfo)]
    msg = sprint(showerror, err)
    sig = get_sig(interp, linfo)
    return GeneratorErrorReport(vst, msg, sig, err)
end

"""
    ExceptionReport <: InferenceErrorReport

The abstract type for "serious" errors that are invoked by `throw` calls but should be
    reported even if they may be caught in actual execution.
In order to avoid duplicated reports for the `throw` call, any subtype of `ExceptionReport`
    should keep `lin::LineInfoNode` field, which represents where the report gets collected.
"""
abstract type ExceptionReport <: InferenceErrorReport end

# # NOTE: this mixin implementation is cleaner but doesn't help inference,
# # because this `getproperty` interface relies on constant prop' and it won't happen when
# # there're multiple applicable methods.
# function Base.getproperty(er::ExceptionReport, sym::Symbol)
#     sym === :lin && return getfield(er, :lin)::LineInfoNode
#     return @invoke getproperty(er::InferenceErrorReport, sym::Symbol)
# end

@reportdef struct UndefKeywordErrorReport <: ExceptionReport
    err::UndefKeywordError
    lin::LineInfoNode
end
get_msg(::Type{UndefKeywordErrorReport}, interp, sv::InferenceState, err::UndefKeywordError, lin::LineInfoNode) = sprint(showerror, err)

"""
    UncaughtExceptionReport <: InferenceErrorReport

Represents general `throw` calls traced during inference.
They are reported only when they're not caught by any control flow.
"""
@reportdef struct UncaughtExceptionReport <: InferenceErrorReport
    throw_calls::Vector{Expr}
end
function UncaughtExceptionReport(interp, sv::InferenceState, throw_calls::Vector{Expr})
    vf = get_virtual_frame(interp, sv.linfo)
    msg = length(throw_calls) == 1 ? "may throw" : "may throw either of"
    sig = Any[]
    ncalls = length(throw_calls)
    for (i, call) in enumerate(throw_calls)
        call_sig = _get_sig(interp, sv, call)
        append!(sig, call_sig)
        i ≠ ncalls && push!(sig, ", ")
    end
    return UncaughtExceptionReport([vf], msg, sig, throw_calls)
end

"""
    NativeRemark <: InferenceErrorReport

This special `InferenceErrorReport` is just for wrapping remarks from `NativeInterpreter`.

!!! note
    Currently JET.jl doesn't make any use of `NativeRemark`.
"""
@reportdef struct NativeRemark <: InferenceErrorReport
    s::String
end
get_msg(::Type{NativeRemark}, interp, sv::InferenceState, s::String) = s

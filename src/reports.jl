# toplevel
# --------

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
# ---------

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

# TODO: maybe we want to use https://github.com/aviatesk/Mixin.jl
"""
    InferenceErrorReport

An interface type of error reports that JET collects by abstract interpration.
All `InferenceErrorReport` should have the following fields:
- `vst::VirtualStackTrace`: a virtual stack trace of the error
- `msg::String`: explains why this error is reported
- `sig::Vector{Any}`: a signature of the error

Note that
- [`@reportdef`](@ref) is the utility macro to define a subtype of `InferenceErrorReport`
- each subtype type of `InferenceErrorReport` may have other arbitrary fields other than
  those mandatory explained above

See also: [`VirtualStackTrace`](@ref), [`VirtualFrame`](@ref), [`@reportdef`](@ref)
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

struct InferenceErrorReportCache
    T::Type{<:InferenceErrorReport}
    vst::VirtualStackTrace
    msg::String
    sig::Vector{Any}
    spec_args::NTuple{N,Any} where N
end

function cache_report!(cache, report::T) where {T<:InferenceErrorReport}
    vst = copy(report.vst)
    new = InferenceErrorReportCache(T, vst, report.msg, report.sig, spec_args(report))
    return push!(cache, new)
end

function restore_cached_report!(cache::InferenceErrorReportCache,
                                interp#=::JETInterpreter=#,
                                )
    report = restore_cached_report(cache)
    if isa(report, UncaughtExceptionReport)
        stash_uncaught_exception!(interp, report)
    else
        report!(interp, report)
    end
    return report
end

function restore_cached_report(cache::InferenceErrorReportCache)
    T = cache.T
    vst = copy(cache.vst)
    return T(vst, cache.msg, cache.sig, cache.spec_args)::InferenceErrorReport
end

"""
    @reportdef SomeErrorReport(interp, sv, args...) [track_from_frame = false] [supertype = InferenceErrorReport]

The utility macro to define `InferenceErrorReport`.
Given a constructor call signature `SomeErrorReport(interp, sv, args...)`, this macro will define:
- `struct` definition for `SomeErrorReport`
- constructor to create `SomeErrorReport` during type inference
- constuctor to restore `SomeErrorReport` from JET's report cache
- getter method to retrieve fields specific to `SomeErrorReport` (which are specified by the `args...` part)

Then `SomeErrorReport` can be created by calling the constructor `SomeErrorReport(interp::JETInterpreter, sv::InferenceState, args...)`
from abstract interpration routine.
"""
macro reportdef(ex, kwargs...)
    T = esc(first(ex.args))
    args = map(ex.args) do x
        # unwrap @nospecialize
        if @isexpr(x, :macrocall) && first(x.args) === Symbol("@nospecialize")
            x = esc(last(x.args)) # `esc` is needed because `@nospecialize` escapes its argument anyway
        end
        return x
    end
    spec_args = args[4:end] # keep those additional, specific fields

    local track_from_frame = false
    local supertype = InferenceErrorReport
    for ex in kwargs
        @assert @isexpr(ex, :(=))
        kw, val = ex.args
        if kw === :track_from_frame
            track_from_frame = val
        elseif kw === :supertype
            supertype = val
        end
    end

    args′ = strip_type_decls.(args)
    spec_args′ = strip_type_decls.(spec_args)
    interp_constructor = Expr(:function, ex, Expr(:block, __source__, quote
        interp = $(args′[2])
        sv = $(args′[3])

        msg = get_msg(#= T, interp, sv, ... =# $(args′...))
        sig = get_sig(#= T, interp, sv, ... =# $(args′...))

        $(if track_from_frame quote
            # when report is constructed _after_ the inference on `sv` has been done,
            # collect location information from `sv.linfo`
            vst = VirtualFrame[get_virtual_frame(interp, sv.linfo)]
        end else quote
            vst = VirtualFrame[get_virtual_frame(interp, sv)]
        end end)

        return new(vst, msg, sig, $(spec_args′...))
    end))

    spec_types = extract_type_decls.(spec_args)

    cache_constructor_sig = :($(T)(st::VirtualStackTrace,
                                   msg::AbstractString,
                                   sig::AbstractVector,
                                   @nospecialize(spec_args),
                                   ))
    cache_constructor_call = :(new(st, msg, sig))
    for (i, spec_type) in enumerate(spec_types)
        push!(cache_constructor_call.args,
              :($(esc(:spec_args))[$(i)]::$(spec_type)), # `esc` is needed because `@nospecialize` escapes its argument anyway
              )
    end
    cache_constructor = Expr(:function, cache_constructor_sig, Expr(:block, __source__,
        :(return @inbounds $(cache_constructor_call))
    ))

    spec_getter_sig = :($(esc(:spec_args))(report::$(T)))
    spec_getter_tuple = Expr(:tuple)
    for spec_arg in QuoteNode.(strip_escape.(spec_args′))
        push!(spec_getter_tuple.args,
              Expr(:call, GlobalRef(Base, :getproperty), :report, spec_arg),
              )
    end
    spec_args_getter = Expr(:function, spec_getter_sig, Expr(:block, __source__,
        :(return $(spec_getter_tuple)::Tuple{$(spec_types...)})
    ))

    return Expr(:block, __source__, quote
        Base.@__doc__ struct $(T) <: $(supertype)
            vst::VirtualStackTrace
            msg::String
            sig::Vector{Any}
            $(spec_args...)

            # constructor from abstract interpretation process by `JETInterpreter`
            $(interp_constructor)

            # constructor from cache
            $(cache_constructor)
        end

        $(spec_args_getter)
    end)
end

function strip_type_decls(x)
    @isexpr(x, :escape) && return Expr(:escape, strip_type_decls(first(x.args))) # keep escape
    return @isexpr(x, :(::)) ? first(x.args) : x
end

strip_escape(x) = @isexpr(x, :escape) ? first(x.args) : x
extract_type_decls(x) = @isexpr(x, :(::)) ? last(x.args) : Any

@reportdef NoMethodErrorReport(interp, sv, unionsplit::Bool, @nospecialize(atype::Type))

@reportdef InvalidBuiltinCallErrorReport(interp, sv, argtypes::Vector{Any})

@reportdef NoFieldErrorReport(interp, sv, @nospecialize(typ::Type), name::Symbol)

@reportdef GlobalUndefVarErrorReport(interp, sv, mod::Module, name::Symbol)

@reportdef LocalUndefVarErrorReport(interp, sv, name::Symbol) track_from_frame = true

@reportdef NonBooleanCondErrorReport(interp, sv, @nospecialize(t::Union{Type,Vector{Type}}))

@reportdef DivideErrorReport(interp, sv)

@reportdef InfiniteIterationErrorReport(interp, sv)

# TODO we may want to hoist `InvalidConstXXX` errors into top-level errors

@reportdef InvalidConstantRedefinition(interp, sv, mod::Module, name::Symbol, @nospecialize(t′), @nospecialize(t))

@reportdef InvalidConstantDeclaration(interp, sv, mod::Module, name::Symbol)

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

@reportdef UndefKeywordErrorReport(interp, sv, err::UndefKeywordError, lin::LineInfoNode) supertype = ExceptionReport

"""
    UncaughtExceptionReport <: InferenceErrorReport

Represents general `throw` calls traced during inference.
They are reported only when they're not caught by any control flow.
"""
@reportdef UncaughtExceptionReport(interp, sv, throw_calls::Vector{Expr}) track_from_frame = true

"""
    NativeRemark <: InferenceErrorReport

This special `InferenceErrorReport` is just for wrapping remarks from `NativeInterpreter`.

!!! note
    Currently JET.jl doesn't make any use of `NativeRemark`.
"""
@reportdef NativeRemark(interp, sv, s::String)

function get_virtual_frame(interp#=::JETInterpreter=#, loc::Union{InferenceState,MethodInstance})
    sig = get_sig(interp, loc)
    file, line = get_file_line(loc)
    linfo = isa(loc, InferenceState) ? loc.linfo : loc
    return VirtualFrame(file, line, sig, linfo)
end

get_file_line(frame::InferenceState) = get_file_line(get_lin(frame))
get_file_line(linfo::LineInfoNode)   = linfo.file, linfo.line
# this location is not exact, but this is whay we know at best
function get_file_line(linfo::MethodInstance)
    def = linfo.def

    isa(def, Method) && return def.file, Int(def.line)

    # toplevel
    src = linfo.uninferred::CodeInfo
    return get_file_line(first(src.linetable::Vector)::LineInfoNode)
end

# adapted from https://github.com/JuliaLang/julia/blob/0f11a7bb07d2d0d8413da05dadd47441705bf0dd/base/show.jl#L989-L1011
function get_sig(interp#=::JETInterpreter=#, l::MethodInstance)
    def = l.def
    ret = if isa(def, Method)
        if isdefined(def, :generator) && l === def.generator
            # print(io, "MethodInstance generator for ")
            # show(io, def)
            sprint(show, def)
        else
            # print(io, "MethodInstance for ")
            @static if hasmethod(Base.show_tuple_as_call, (IO, Symbol, Type), (:demangle, :kwargs, :argnames, :qualified))
                # show_tuple_as_call(io, def.name, l.specTypes; qualified=true)
                sprint((args...)->Base.show_tuple_as_call(args...; qualified=true), def.name, l.specTypes)
            else
                # show_tuple_as_call(io, def.name, l.specTypes, false, nothing, nothing, true)
                sprint(Base.show_tuple_as_call, def.name, l.specTypes, false, nothing, nothing, true)
            end
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

# entry
get_sig(::Type{<:InferenceErrorReport}, interp#=::JETInterpreter=#, sv, @nospecialize(args...)) = get_sig(interp, sv)
get_sig(interp#=::JETInterpreter=#, sv::InferenceState) = _get_sig(interp, sv, get_stmt(sv))

# special cased entries
get_sig(::Type{LocalUndefVarErrorReport}, interp#=::JETInterpreter=#, sv, name) = Any[""] # TODO
function get_sig(::Type{UncaughtExceptionReport}, interp#=::JETInterpreter=#, sv, throw_calls)
    sig = Any[]
    ncalls = length(throw_calls)
    for (i, call) in enumerate(throw_calls)
        call_sig = _get_sig(interp, sv, call)
        append!(sig, call_sig)
        i ≠ ncalls && push!(sig, ", ")
    end
    return sig
end

_get_sig(args...) = first(_get_sig_type(args...))::Vector{Any}

function _get_sig_type(interp#=::JETInterpreter=#, sv::InferenceState, expr::Expr)
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

            sig = _get_sig(interp, sv, f)
            push!(sig, '(')

            nargs = length(args)
            for (i, arg) in enumerate(args)
                arg_sig = _get_sig(interp, sv, arg)
                append!(sig, arg_sig)
                i ≠ nargs ? push!(sig, ", ") : push!(sig, "...)")
            end
        else
            sig = _get_sig(interp, sv, f)
            push!(sig, '(')

            nargs = length(args)
            for (i, arg) in enumerate(args)
                arg_sig = _get_sig(interp, sv, arg)
                append!(sig, arg_sig)
                i ≠ nargs && push!(sig, ", ")
            end
            push!(sig, ')')
        end

        return sig, nothing
    elseif head === :(=)
        return _get_sig_type(interp, sv, last(expr.args))
    elseif head === :static_parameter
        typ = widenconst(sv.sptypes[first(expr.args)])
        return Any['_', typ], typ
    else
        return Any[string(expr)], nothing
    end
end
function _get_sig_type(interp#=::JETInterpreter=#, sv::InferenceState, ssa::SSAValue)
    sig, sig_typ = _get_sig_type(interp, sv, sv.src.code[ssa.id])
    typ = widenconst(ignorelimited(ignorenotfound(sv.src.ssavaluetypes[ssa.id])))
    sig_typ == typ || push!(sig, typ)
    return sig, typ
end
function _get_sig_type(interp#=::JETInterpreter=#, sv::InferenceState, slot::SlotNumber)
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
_get_sig_type(interp#=::JETInterpreter=#, ::InferenceState, gr::GlobalRef) = Any[string(gr.mod, '.', gr.name)], nothing
function _get_sig_type(interp#=::JETInterpreter=#, sv::InferenceState, s::Symbol)
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
function _get_sig_type(interp#=::JETInterpreter=#, sv::InferenceState, rn::ReturnNode)
    sig = is_unreachable(rn) ? Any["unreachable"] : Any["return ", _get_sig(interp, sv, rn.val)...]
    return sig, nothing
end
function _get_sig_type(interp#=::JETInterpreter=#, ::InferenceState, qn::QuoteNode)
    typ = typeof(qn.value)
    return Any[string(qn), typ], typ
end
_get_sig_type(interp#=::JETInterpreter=#, ::InferenceState, @nospecialize(x)) = Any[repr(x; context = :compact => true)], nothing

# TODO count invalid unon split case
get_msg(::Type{NoMethodErrorReport}, interp, sv, unionsplit, @nospecialize(args...)) = unionsplit ?
    "for any of the union split cases, no matching method found for call signature" :
    "no matching method found for call signature"
get_msg(::Type{InvalidBuiltinCallErrorReport}, interp, sv, @nospecialize(args...)) =
    "invalid builtin function call"
get_msg(::Type{NoFieldErrorReport}, interp, sv, @nospecialize(typ), name) =
    "type $(typ) has no field $(name)"
get_msg(::Type{GlobalUndefVarErrorReport}, interp, sv, mod, name) =
    "variable $(mod).$(name) is not defined"
get_msg(::Type{LocalUndefVarErrorReport}, interp, sv, name) =
    "local variable $(name) is not defined"
get_msg(::Type{NonBooleanCondErrorReport}, interp, sv, @nospecialize(t::Type)) =
    "non-boolean ($t) used in boolean context"
get_msg(::Type{NonBooleanCondErrorReport}, interp, sv, ts::Vector{Type}) =
    "for $(length(ts)) of union split cases, non-boolean ($(join(ts, ','))) used in boolean context"
@eval get_msg(::Type{DivideErrorReport}, interp, sv) = $(let
    io = IOBuffer()
    showerror(io, DivideError())
    String(take!(io))
end)
get_msg(::Type{InvalidConstantRedefinition}, interp, sv, mod, name, @nospecialize(t′), @nospecialize(t)) =
    "invalid redefinition of constant $(mod).$(name) (from $(t′) to $(t))"
get_msg(::Type{InvalidConstantDeclaration}, interp, sv, mod, name) =
    "cannot declare a constant $(mod).$(name); it already has a value"
get_msg(::Type{UndefKeywordErrorReport}, interp, sv, err, lin) = sprint(showerror, err)
get_msg(::Type{UncaughtExceptionReport}, interp, sv, throw_blocks) = isone(length(throw_blocks)) ?
    "may throw" :
    "may throw either of"
get_msg(::Type{NativeRemark}, interp, sv, s) = s
get_msg(::Type{InfiniteIterationErrorReport}, interp, sv) =
    "invalid return type for `iterate` method; should be Union{Nothing, Tuple{Any, Any}}"

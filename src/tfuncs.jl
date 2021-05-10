# TODO: set up our own tfuncs

function CC.builtin_tfunction(interp::JETInterpreter, @nospecialize(f), argtypes::Array{Any,1},
                              sv::InferenceState) # `JETInterpreter` isn't overloaded on `return_type`
    ret = @invoke builtin_tfunction(interp::AbstractInterpreter, f, argtypes::Array{Any,1},
                                    sv::Union{InferenceState,Nothing})

    if f === throw
        # here we only report a selection of "serious" exceptions, i.e. those should be
        # reported even if they may be caught in actual execution;
        # other general `throw` calls will be reported within `_typeinf(interp::JETInterpreter, frame::InferenceState)`
        # only when they are not caught by control flow, which is judged by whether if the
        # final return type of `sv` is annotated as `Bottom` or not
        if length(argtypes) ≥ 1
            a = first(argtypes)
            if isa(a, Const)
                v = a.val
                if isa(v, UndefKeywordError)
                    report!(sv, UndefKeywordErrorReport(interp, sv, v, get_lin(sv)))
                end
            end
        end
        return ret
    elseif f === getfield
        # `getfield` is so common, let's special case it
        if 2 ≤ length(argtypes) ≤ 3
            obj, fld = argtypes
            if isa(fld, Const)
                name = fld.val
                if isa(name, Symbol)
                    if isa(obj, Const) && (mod = obj.val; isa(mod, Module))
                        if isdefined(mod, name)
                            if istoplevel_globalref(interp, sv)
                                # when accessing to a global variable in a module concretized by `interp`,
                                # take a risk and eagerly propagate its type
                                # NOTE logic here should be synced with that of `abstract_eval_special_value(::JETInterpreter, ::Any, ::VarTable, ::InferenceState)`
                                val = getfield(mod, name)
                                return isa(val, AbstractGlobal) ? val.t : Const(val)
                            end
                            # TODO; `ret` should be `Any` here, add report pass here (for performance linting)
                        else
                            # report access to undefined global variable
                            report!(sv, GlobalUndefVarErrorReport(interp, sv, mod, name))
                            # return Bottom
                        end
                    elseif ret === Bottom
                        # general case when an error is detected by the native `getfield_tfunc`
                        typ = widenconst(obj)
                        report!(sv, NoFieldErrorReport(interp, sv, typ, name))
                        return ret
                    end
                end
            end
        end
    elseif f === fieldtype
        # the valid widest possible return type of `fieldtype_tfunc` is `Union{Type,TypeVar}`
        # because fields of unwrapped `DataType`s can legally be `TypeVar`s,
        # but this will cause lots of false positive `NoMethodErrorReport`s for inference
        # with accessing to abstract fields since most methods don't expect `TypeVar`
        # (e.g. `@report_call readuntil(stdin, 'c')`)
        # JET.jl further widens this case to `Any` and give up further analysis rather than
        # trying hard to do sound and noisy analysis
        # xref: https://github.com/JuliaLang/julia/pull/38148
        if ret === Union{Type, TypeVar}
            return Any
        end
    elseif length(argtypes) == 2 && begin
            f === Intrinsics.checked_sdiv_int ||
            f === Intrinsics.checked_srem_int ||
            f === Intrinsics.checked_udiv_int ||
            f === Intrinsics.checked_urem_int
        end
        # `DivideError` for these intrinsics are handled in C and should be special cased
        a = argtypes[2]
        t = widenconst(a)
        if t <: Base.BitSigned64 || t <: Base.BitUnsigned64
            if isa(a, Const) && a.val === zero(t)
                report!(sv, DivideErrorReport(interp, sv))
                return Bottom
            end
        end
    end

    if ret === Bottom
        # XXX: for general case, JET just relies on the (maybe too persmissive) return type
        # from native tfuncs to report invalid builtin calls and probably there're lots of
        # false negatives
        report!(sv, InvalidBuiltinCallErrorReport(interp, sv, argtypes))
    end

    return ret
end

# check if this frame is for `getproperty(::Module, ::Symbol)`, which accesses to a global
# variable traced by `interp`
function istoplevel_globalref(interp::JETInterpreter, sv::InferenceState)
    def = sv.linfo.def
    def.name === :getproperty || return false
    def.sig === Tuple{typeof(getproperty), Module, Symbol} || return false
    parent = sv.parent
    return !isnothing(parent) && istoplevel(interp, parent)
end

# `return_type_tfunc` internally uses `abstract_call` to model `return_type` function and
# here we shouldn't pass `JETInterpreter` to it; otherwise we may get false error reports from
# the  `abstract_call`, which isn't the abstraction of actual execution, thus here we just
# check if the call of `return_type` is valid or not
function CC.return_type_tfunc(interp::JETInterpreter, argtypes::Vector{Any}, sv::InferenceState)
    if length(argtypes) ≠ 3
        # invalid argument number, let's report and return error result (i.e. `Bottom`)
        report!(sv, NoMethodErrorReport(interp,
                                        sv,
                                        # this is not necessary to be computed correctly, though
                                        argtypes_to_type(argtypes),
                                        ))
        @static if isdefined(CC, :ReturnTypeCallInfo)
            return CallMeta(Bottom, nothing)
        else
            return Bottom
        end
    else
        # don't recursively pass on `JETInterpreter` via `@invoke`
        return return_type_tfunc(interp.native, argtypes, sv)
    end
end

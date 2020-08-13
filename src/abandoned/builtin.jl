# TODO: implement type-check functions

"""
    ret = maybe_profile_builtin_call!(frame, call_ex)

If `call_ex` is a builtin call, profile it and return its return type,
  otherwise, return `call_argtypes` that represents call argument types of the
  (non-builtin) call.

For this function to work, `frame.src` _**should**_ be a typed IR.
Then a builtin call has already been through the abstract interpretation by
  [`Core.Compiler.abstract_call_known`](@ref), and then we can trust its
  result and report an error if the return type is [`Union{}`](@ref).

!!! warning
    For `Core.IntrinsicFunction`s, [`Core.Compiler.builtin_tfunction`](@ref) only
      performs really rough estimation of its return type.
    Accordingly this function also can mis-profile errors in intrinsic function calls.
"""
function maybe_profile_builtin_call!(frame, call_ex)
  call_argtypes = collect_call_argtypes(frame, call_ex)
  any(==(Unknown), call_argtypes) && return Unknown

  ftyp = call_argtypes[1]
  !<:(ftyp, Core.Builtin) && return call_argtypes

  rettyp = frame.src.ssavaluetypes[frame.pc]
  # Union{} usually means the inference catches an error in this call
  if rettyp == Union{}
    # TODO: handle exceptions somehow
    # throw accepts any type of object and TP currently just ignores them
    ftyp == typeof(throw) && return rettyp

    tt = to_tt(call_argtypes)
    @report!(frame, InvalidBuiltinCallErrorReport(tt))
  end

  # TODO:
  # this pass should be validated with type-check functions for builtin calls
  # just relying on Julia's inference result includes obvious false negative case,
  # e.g. `getfield` will always return `Any` if its first argument is `Any`
  return rettyp
end
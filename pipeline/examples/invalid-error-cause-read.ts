// The error's own `cause` is not stated: a read of it is refused.
export function read(): unknown {
  return new Error("x", { cause: 1 }).cause;
}

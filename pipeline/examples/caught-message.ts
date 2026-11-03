// A caught value's message read without running its code: a primitive by
// `String`; of an object, the string it owns at `message` as a data
// property, `Object.getOwnPropertyDescriptor(o, k)?.value` bound to a
// constant read only through `typeof … === "string"` (`%OwnString%`), which
// calls no getter and admits a host object; an `Error` owning no message
// reads `""`, any other object a fixed text (run under Node:
// `tests/tool-failures.mts`).
// Census: thrown.mts#ioFailure reads a caught value's message through messageOf.
export function messageOf(thrown: unknown): string {
  if (
    thrown === null ||
    (typeof thrown !== "object" && typeof thrown !== "function")
  )
    return String(thrown);
  const message: unknown = Object.getOwnPropertyDescriptor(
    thrown,
    "message",
  )?.value;
  if (typeof message === "string") return message;
  return thrown instanceof Error && !Object.hasOwn(thrown, "message")
    ? ""
    : "a thrown object that owns no string message";
}

export function firstLine(thrown: unknown): string {
  const own = Object.getOwnPropertyDescriptor(thrown ?? {}, "message")?.value;
  return "string" !== typeof own ? "" : (own.split("\n")[0] ?? "");
}

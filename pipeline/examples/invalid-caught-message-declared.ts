// The descriptor's value of a caught object, declared `string` rather than
// tested: TypeScript reads `PropertyDescriptor`'s `value` as `any`, so the
// declaration passes, but an object holding `Error.prototype` may own a
// `message` of any type (run under Node: a number). Its references are
// typed by the declaration, not by a `typeof` test, so the read is no
// `%OwnString%`, and the descriptor's operand, `object`, may be a host
// object: refused.
export function messageOf(thrown: object): string {
  const message: string = Object.getOwnPropertyDescriptor(
    thrown,
    "message",
  )?.value;
  return message;
}

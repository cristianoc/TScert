// An optional call through a `let` the loop assigns: the receiver is
// `undefined` on the first iteration and an array afterwards. A pass that
// finds the receiver only nullish claims the call's body at no value, being
// unreached; the loop's settled pass claims it at the array.
export function collect(lines: string[], into: string[]): number {
  let target: string[] | undefined;
  for (const line of lines) {
    target?.push(line);
    target = into;
  }
  return into.length;
}

// A receiver only `undefined` where the call runs: the body is never
// reached.
export function unreached(into: string[]): number {
  let target: string[] | undefined;
  target?.push("x");
  target = into;
  return target.length;
}

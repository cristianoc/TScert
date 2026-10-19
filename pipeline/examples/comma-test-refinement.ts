// A comma in a test position (SOURCE-ELABORATION.md, "Derived source
// forms"): the left operand runs for its effects, then the right operand is
// the test, refining in the state the left one leaves, on both edges, in a
// condition, a conditional, and beside `&&`, `||` and `!`.
type A = { readonly kind: 1; readonly a: string };
type B = { readonly kind: 2; readonly b: string };
type C = { readonly kind: 3; readonly c: string };

export function cond(x: A | B | C): string {
  if ((x satisfies A | B | C, x.kind === 1 || x.kind === 2)) return x.kind === 1 ? x.a : x.b;
  return x.c;
}

export function ternary(x: A | B | C): string {
  return (x satisfies A | B | C, x.kind === 3) ? x.c : "";
}

export function conjunction(x: A | B | C): string {
  return (x satisfies A | B | C, x.kind === 3) && x.c ? x.c : "";
}

export function negation(x: A | B | C): string {
  return !(x satisfies A | B | C, x.kind !== 3) ? x.c : "";
}

export function counted(x: A | B | C): number {
  const box = { count: 0 };
  return (box.count++, x.kind === 1) ? box.count : -box.count;
}

// The test reads what the left operand wrote: `n` holds 5 when it runs.
export function written(): 5 | 0 {
  let n: number = 0;
  return (n = 5, n === 5) ? n : 0;
}

// A left operand that throws leaves the test unreached; the call's
// exception is the comma's.
const fail = (message: string): never => {
  throw new Error(message);
};

export function thrown(x: A | B | C): string {
  return (fail("left"), x.kind === 3) ? x.c : "";
}

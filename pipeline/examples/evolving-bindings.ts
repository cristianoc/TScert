// TypeScript's evolving `any`: an unannotated `let` initialized with `null`
// or `undefined` holds what is assigned to it, and an unannotated `[]` the
// elements pushed or written into it. The binding's contract is the union of
// those, TypeScript's evolved type; every write is checked against it, and
// a closure reading the binding later knows it by that contract.
export function maybe(flag: boolean): number | null {
  let v = null;
  if (flag) v = 1;
  return v;
}
export function incremented(xs: number[]): number[] {
  const values = [];
  for (const x of xs) values.push(x + 1);
  return values;
}
export function written(): string[] {
  const out = [];
  out[0] = "a";
  out.unshift("b");
  return out;
}
export function captured(): number {
  let value = null;
  value = 1;
  const read = (): number => {
    if (value !== null) return value;
    return 0;
  };
  value = null;
  return read();
}
export function later(): number {
  let u = undefined;
  u = "s";
  const s: string | undefined = u;
  return s === undefined ? 0 : s.length;
}

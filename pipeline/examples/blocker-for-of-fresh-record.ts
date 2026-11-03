// A loop that replaces a binding's record with a fresh one on each pass.
// Census functions:
// fragment-expressions.mts#template (written as a reduce).
type S = { k: "lit"; v: string };
export function last(xs: readonly string[], e: S): S {
  let acc: S = e;
  for (const x of xs) acc = { k: "lit", v: x };
  return acc;
}

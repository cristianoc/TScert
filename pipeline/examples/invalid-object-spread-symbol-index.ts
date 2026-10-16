// JavaScript's copy also takes an own enumerable symbol-keyed property, which
// a type stating no symbol key says nothing of: `{ [s]: "x" }` is a
// `{ [k: string]: number }`, and its copy holds a string under `s`.
export function open(a: { [k: string]: number }): {
  [k: string]: number;
  [k: symbol]: number;
} {
  return { ...a };
}

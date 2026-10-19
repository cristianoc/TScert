// Node's `structuredClone` of any value: a copy read at `unknown`, no effect
// stated.
export function copy(value: { readonly a: number }): unknown {
  return structuredClone(value);
}

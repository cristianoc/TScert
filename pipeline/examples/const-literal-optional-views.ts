// A constant's object literal used whole where a type with an optional field
// it leaves out is expected is claimed with its exact keys: the bound says
// it lacks the key, so it meets each such view, readonly or writable, and a
// dictionary of no value.
export function views(): void {
  const t = {};
  const f: { a?: number } = t;
  const g: { b?: string } = t;
  const r: { readonly a?: number } = t;
}

export function never(): void {
  const t = {};
  const b: { [k: string]: never } = t;
  const c: { a?: number } = t;
}

export function fields(): number {
  const t = { x: 1 };
  const o: { x: number; y?: string } = t;
  return o.x;
}

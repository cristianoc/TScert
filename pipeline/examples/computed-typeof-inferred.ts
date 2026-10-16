// `typeof x` of a constant without an annotation is the type TypeScript
// infers for it: an object literal's is a record of writable fields.
const origin = { x: 0, label: "o", inner: { y: true } };
export function copy(p: typeof origin): number {
  p.x = p.x + 1;
  return p.inner.y ? p.x : p.label.length;
}

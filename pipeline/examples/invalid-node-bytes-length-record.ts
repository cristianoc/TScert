// A spread copies a record's own properties, and a view of bytes holds
// `length` on its prototype chain (run under Node: the copy's `length` is
// `undefined`): a `Uint8Array` meets no record naming `length`, refused.
function copied(x: { readonly length: number }): number {
  return { ...x }.length;
}
export function measured(bytes: Uint8Array): number {
  return copied(bytes);
}

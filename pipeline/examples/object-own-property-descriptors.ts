// `Object.getOwnPropertyDescriptors` of a record: a fresh dictionary of
// fresh descriptors, each `value` `unknown`, their fields writable. Its
// descriptors are read through `Object.values` and written, as
// recoverGate reads and writes them.
// Census functions: diagnostic-gate.mts#recoverGate.
export function snapshot(o: { a: number; b: string }): unknown[] {
  const descriptors = Object.getOwnPropertyDescriptors(o);
  const values: unknown[] = [];
  for (const descriptor of Object.values(descriptors)) {
    descriptor.enumerable = false;
    values.push(descriptor.value);
  }
  return values;
}

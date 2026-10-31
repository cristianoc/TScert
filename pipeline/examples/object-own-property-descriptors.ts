// `Object.getOwnPropertyDescriptors` of a record: a fresh dictionary of
// fresh descriptors, each `value` `unknown`, their fields writable. Its
// descriptors are read through `Object.values`; each descriptor
// has `enumerable` set to false and its `value` collected.
export function snapshot(o: { a: number; b: string }): unknown[] {
  const descriptors = Object.getOwnPropertyDescriptors(o);
  const values: unknown[] = [];
  for (const descriptor of Object.values(descriptors)) {
    descriptor.enumerable = false;
    values.push(descriptor.value);
  }
  return values;
}

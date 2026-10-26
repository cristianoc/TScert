// `Object.hasOwn` of an object at a string key: a Boolean, read without
// running code; no value of the object reaches the program.
export function owns(table: { readonly [key: string]: number }, key: string): boolean {
  return Object.hasOwn(table, key);
}

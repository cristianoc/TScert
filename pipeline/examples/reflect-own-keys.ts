// `Reflect.ownKeys(o)` of a value that is no host object: its own keys,
// strings and symbols, in a fresh array, read without running code.
// Census functions: family-activation.mts#enumObjectMatches,
// family-activation.mts#tagEnumMatches.
export function onlyNamed(record: { [key: string]: number }, names: ReadonlySet<string>): boolean {
  return Reflect.ownKeys(record).every(key => typeof key === "string" && names.has(key));
}
export function keysAdded(point: { x: number; y: number }): (string | symbol)[] {
  const keys = Reflect.ownKeys(point);
  keys.push("added");
  return keys;
}

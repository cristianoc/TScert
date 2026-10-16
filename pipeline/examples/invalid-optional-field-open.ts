// A record that does not name the key may still hold it, at any type: it does
// not establish the optional field. (TypeScript accepts this.)
function read(value: { field?: number }): number | undefined {
  return value.field;
}
export function pass(value: { other: number }): number | undefined {
  return read(value);
}

// Undefined at the root serializes to undefined, outside the string result.
export function wrong(): string {
  return JSON.stringify(undefined);
}

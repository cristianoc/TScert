// `"length" in bytes` is true of a view of bytes (run under Node), whose
// `length` is its prototype chain's: refused.
export function measured(bytes: Buffer): boolean {
  return "length" in bytes;
}

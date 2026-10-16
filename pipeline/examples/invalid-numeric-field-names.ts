// `0x10` is the key "16", not "10".
export function bad(x: { 0x10: string }): { 10: string } {
  return x;
}

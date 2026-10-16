// `x[0x10]` reads the property "16", a string here, not "10".
export function bad(x: { 16: string; 10: number }): number {
  return x[0x10];
}

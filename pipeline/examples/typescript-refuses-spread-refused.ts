// A spread of an array of unknown length into fixed parameters, which the
// producer refuses and TypeScript rejects too (TS2556): the refusal is named
// by TypeScript's error.
function three(a: number, b: number, c: number): number {
  return a + b + c;
}
export function sum(xs: number[]): number {
  return three(...xs);
}

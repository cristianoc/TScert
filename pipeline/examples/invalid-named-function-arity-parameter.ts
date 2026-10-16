// A module function meets a longer signature only where its own parameters
// accept the signature's leading ones: here a string parameter at a number.
function one(x: string): string {
  return x.toUpperCase();
}
export function widen(): (a: number, b: string) => string {
  return one;
}

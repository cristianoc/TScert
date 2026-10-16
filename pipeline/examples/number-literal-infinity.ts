// A numeric literal past the largest double, `1e309`, is the infinity it
// rounds to, as a literal type and as a value; a hexadecimal literal is its
// decimal value.
export function inf(x: 1e309, y: 2e309): boolean {
  return x === y;
}
export function big(): 1e309 {
  return 1e309;
}
export function hex(): 31 {
  return 0x1f;
}

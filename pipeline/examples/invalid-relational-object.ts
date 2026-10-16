// An object operand of `<` converts through its own `valueOf`, which runs the
// program's code: refused, although TypeScript accepts it.
interface Reading {
  valueOf(): number;
}
function earlier(a: Reading, b: Reading): boolean {
  return a < b;
}

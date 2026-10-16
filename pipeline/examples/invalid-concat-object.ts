// An object converts to a string through its own methods, which may run any
// code: refused, though TypeScript accepts it.
function show(o: { a: number }): string {
  return "o=" + o;
}

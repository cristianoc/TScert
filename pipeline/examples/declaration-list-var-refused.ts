// A `var` list of patterns is function-scoped and hoisted, outside the
// fragment's lexical declarations.
export function sum(): number {
  var { x } = { x: 1 }, { y } = { y: 2 };
  return x + y;
}

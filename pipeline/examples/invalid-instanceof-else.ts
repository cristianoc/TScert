// Where `instanceof Array` fails the value is not an array: a tuple does not
// survive to that arm.
function first(x: [number, string] | number): [number, string] {
  if (x instanceof Array) return [0, ""];
  return x;
}

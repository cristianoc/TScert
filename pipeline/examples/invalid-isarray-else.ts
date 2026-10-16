// Where `Array.isArray` fails the value is not an array: a tuple does not
// survive to that arm, and neither does a claim that the value is one.
function first(x: [number, string] | number): [number, string] {
  if (Array.isArray(x)) return [0, ""];
  return x;
}

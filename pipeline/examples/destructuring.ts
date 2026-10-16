// Patterns on `const`: the initializer once, then each property or position
// read in pattern order, a default only where the read is undefined.
type Maybe = number | undefined;

function objectDefault(x: { f?: number }): number {
  const { f = 1 } = x;
  return f;
}
// The default removes `undefined` behind a declared alias too: the read is
// told apart clause by clause.
function aliasDefault(x: { f: Maybe }): number {
  const { f = 1 } = x;
  return f;
}
// A union of records reads each alternative as it reads.
function unionDefault(
  x: { f: number } | { f?: string },
): number | string | boolean {
  const { f = true } = x;
  return f;
}
function nested(x: { child: { a?: number; b: number } }): number {
  const {
    child: { a = 0, b },
  } = x;
  return a + b;
}
// A hole skips a position; any array value is read by position, as its
// iterator yields it.
function holes(arr: [number, string, boolean]): boolean {
  const [first, , third] = arr;
  return third;
}
function arrayDefault(values: (number | undefined)[]): number {
  const [value = 0] = values;
  return value;
}
// The rest of a tuple of required positions is a fresh array of the
// positions after the elements.
function restFromTuple(tuple: [number, string, boolean]): [string, boolean] {
  const [first, ...rest] = tuple;
  return rest;
}
function laterDefault(source: { first?: number; later?: number }): number {
  const { later = 2, first = later } = source;
  return first;
}
function swap(): number {
  let p: number = 1;
  let q: number = 2;
  [p, q] = [q, p];
  return p;
}
function assignedRest(): number[] {
  let x: number = 0;
  let r: number[] = [];
  [x, ...r] = [1, 2, 3];
  return r;
}

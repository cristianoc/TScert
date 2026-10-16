// A function reaches the file's other functions at their annotated
// signatures: a direct call, a nested call, rest parameters of both kinds,
// and a parameter that shadows a module function of the same name.
function id(x: boolean): boolean {
  return x;
}
export function twice(x: boolean): boolean {
  return id(id(x));
}
function first(...xs: [boolean, null]): boolean {
  return xs[0];
}
function discard(...xs: boolean[]): null {
  return null;
}
export function spread(x: boolean): boolean {
  discard(x, x, x);
  return first(x, null);
}
export function shadowed(id: null): null {
  return id;
}

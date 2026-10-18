// A slot declared at an alias whose definition names a type parameter holds
// every arm of it after a write, the parameter's among them.
type V<T> = string | T;
export function last<T>(x: V<T>, y: V<T>): V<T> {
  let r: V<T> = x;
  r = y;
  return r;
}

// A parameter of a union with one bare binder: each part of the actual goes
// to the arm of its kind, and the rest to the binder. A ground arm takes only
// a part it names, so an object it does not describe instantiates the binder.
type ObjA = { a: number };
type ObjB = { a: string };
function takeObjAOrT<T>(x: ObjA | T): T | ObjA {
  return x;
}
function objectToBinder(): ObjB | ObjA {
  const b: ObjB = { a: "hello" };
  return takeObjAOrT(b);
}
function maybe<T>(x: T | undefined): T | undefined {
  return x;
}
function primitiveToBinder(n: number | undefined): number | undefined {
  return maybe(n);
}

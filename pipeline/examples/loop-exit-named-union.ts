// A loop over a mutable local holding a named union of records, left when
// the local is falsy or a guard accepts it (`functionOf`'s shape): the exit
// joins the guards' edges, which keep the named union, so the local's claim
// there holds it beside the guards' types.
interface A {
  readonly kind: "a";
  readonly parent: Item | undefined;
}
interface B {
  readonly kind: "b";
  readonly parent: Item | undefined;
}
interface C {
  readonly kind: "c";
  readonly parent: Item | undefined;
}
type Item = A | B | C;
type Owner = B | C;
declare function isOwner(n: Item): n is Owner;
declare function isC(n: Item): n is C;
export function owner(n: Item): Item {
  let at: Item | undefined = n.parent;
  while (at && !isOwner(at) && !isC(at)) at = at.parent;
  return at ?? n;
}

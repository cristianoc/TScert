// A test of a field the arms of a union state as readonly views narrows the
// union, as a test of an invariant field does: a readonly view of a location
// constrains its stored contract, which the object keeps for its lifetime.
type Shape =
  | { readonly k: "a"; readonly x: number }
  | { readonly k: "b"; readonly y: string };

export function measure(o: Shape): number {
  return o.k === "a" ? o.x : o.y.length;
}

type Coded =
  | { readonly code: 1; readonly x: number }
  | { readonly code: 2; readonly y: string }
  | { readonly code: 3 | 4 };

export function decode(o: Coded): number {
  if (o.code === 1) return o.x;
  if (o.code === 2) return o.y.length;
  return 0;
}

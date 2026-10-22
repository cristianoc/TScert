// A `findIndex` callback calling a module function, itself recursive: the
// call reads the function's binding, which nothing reassigns, at the
// effect certified from its body (it changes no storage), so the callback
// is within the empty footprint and each visit passes an element at `Tree`.
type Tree = { readonly leaf: boolean; readonly children: readonly Tree[] };

function closed(t: Tree): boolean {
  return (
    t.leaf || (t.children.length > 0 && t.children.every((c) => closed(c)))
  );
}

export function firstClosed(list: readonly Tree[]): number {
  return list.findIndex((t) => closed(t));
}

// The same call through a fresh literal's field, whose contract is inferred
// from its initialiser, the function's certified signature, and checked at
// every write.
export function firstClosedField(list: readonly Tree[]): number {
  const test = { check: (t: Tree): boolean => closed(t) };
  return list.findIndex((t) => test.check(t));
}

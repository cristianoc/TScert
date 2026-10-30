// A `find` callback calling a method on a union of two records each holding
// it: the member is bound to the object and called at the signatures the
// arms state, ordinary arrows, which may change any storage. So the
// callback is the unrestricted one, whose element is `Bag | Box |
// undefined`: a method written there shrinks the list and is handed
// `undefined` on the next visit.
interface Bag {
  size: number;
  shrink(item: Bag | Box): boolean;
}

interface Box {
  label: string;
  shrink(item: Bag | Box): boolean;
}

export function wrong(
  xs: readonly (Bag | Box)[],
  by: Bag | Box,
): Bag | Box | undefined {
  return xs.find((x) => by.shrink(x));
}

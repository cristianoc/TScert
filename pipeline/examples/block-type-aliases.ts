type Pair = { left: number; right: number };

// A type alias and an interface declared in a body: no execution, a name
// over their block.
function sum(left: number, right: number): number {
  type Point = { x: number; y: number };
  interface Labelled {
    label: string;
    point: Point;
  }
  const point: Point = { x: left, y: right };
  const labelled: Labelled = { label: "p", point };
  return labelled.point.x + point.y;
}

// A generic alias closing over the enclosing function's type parameter.
function wrap<T>(value: T): { item: T; items: T[] } {
  type Holder<U> = { item: T; items: U[] };
  const holder: Holder<T> = { item: value, items: [value] };
  return holder;
}

// A local alias shadowing a module alias: inside the block `Pair` is the
// local one, outside it the module's.
function shadowed(seed: string): number {
  const outer: Pair = { left: 1, right: 2 };
  {
    type Pair = { left: string };
    const inner: Pair = { left: seed };
    return outer.left + inner.left.length;
  }
}

// A local alias referring to another declared after it in the same block,
// and a recursive one.
function chain(n: number): number {
  type Outer = { inner: Inner };
  type Inner = { n: number };
  type List = { head: number; tail: List | null };
  const list: List = { head: n, tail: { head: n, tail: null } };
  const outer: Outer = { inner: { n } };
  return outer.inner.n + list.head;
}

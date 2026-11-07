// A field write replacing the array whose length bounded the index: the
// path's location held an object, which a write of an array field may
// change. Under Node, `counted({ data: [1, 2], count: 0 }, 1)` reads index 1
// of `[]`, `undefined` at `number`.

type Holder = { data: number[]; count: number };

/** @requires safeInteger(i) && 0 <= i && i < o.data.length */
export function counted(o: Holder, i: number): number {
  o.data = [];
  return o.data[i]!;
}

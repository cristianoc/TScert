// Where `Array.isArray` holds, a record arm is a built-in array, but of
// unknown elements and read only: the mutable view the array arm allows
// would let a value be pushed onto an array whose elements have another
// contract.
type Foo = { a: string; b: number };

export function grow(x: unknown[] | Foo): number {
  if (Array.isArray(x)) {
    const y: unknown[] = x;
    y.push(1);
  }
  return 0;
}

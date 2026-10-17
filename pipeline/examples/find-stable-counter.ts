// A `find` callback counting its visits in an outer variable: the callback
// is within `{value: any, store: keep}`, so the receiver's store, and its
// length, stay as they were, and each visit passes an element at `string`.
export function firstLong(xs: string[]): number {
  let visits = 0;
  const found = xs.find((x: string): boolean => {
    visits = visits + 1;
    return x.length > 3;
  });
  return visits + (found === undefined ? 0 : found.length);
}

// A tuple literal built at a binder's tuple bound must meet it: `2` is not
// the bound's `1`.
declare function exact<K extends [0, 1]>(x: K): K;

export function mismatch(): [0, 1] {
  return exact([0, 2]);
}

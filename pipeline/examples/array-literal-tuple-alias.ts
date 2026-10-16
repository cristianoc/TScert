// A fresh array literal expected at a generic tuple alias at arguments is
// built at the alias's equation: `["a", [1, 2]]` is an `Entry<string,
// number>`, a pair, where alone it would be `(string | number[])[]`.
type Entry<K, V> = [K, V[]];

function count(initial?: Entry<string, number>[]): number {
  return initial === undefined ? 0 : initial.length;
}

export function seeded(): number {
  return count([["a", [1, 2]]]) + count([]) + count();
}

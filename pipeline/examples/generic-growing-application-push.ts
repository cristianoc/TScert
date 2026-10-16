// Calling push substitutes string for U in the recursive result family:
// relating Pair<[number, U]> at U = string to the written Pair<[number,
// string]> needs `Pair`'s variance declaration (`Var`, RECURSIVE-EQUATIONS
// §7.5), the two tuples being different heads.
interface Pair<T> {
  first(): T;
  push<U>(u: U): Pair<[T, U]>;
}
export function one(p: Pair<number>): Pair<[number, string]> {
  return p.push("a");
}

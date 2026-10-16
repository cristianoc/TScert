// A recursive bound: `Node`'s own bound `Node<T>` is checked under
// `T extends Node<T>`, and `Leaf` meets `Node<Leaf>`.
interface Node<T extends Node<T>> {
  next: T | null;
}
interface Leaf extends Node<Leaf> {}
export function f(x: Leaf): Leaf | null {
  return x.next;
}

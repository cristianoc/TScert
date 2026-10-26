// Mapped types whose value is `X[P]` at named types applied at arguments,
// reached through an alias, and at a recursive interface: the shape is the
// definition's at the arguments, one unfolding, so a field naming the
// interface keeps its reference (rule mapped-identity).
interface Box<T> {
  value: T;
  readonly label: string;
}
type NumberBox = Box<number>;
interface Node {
  value: number;
  next?: Node;
}

export function boxed(b: Partial<Box<number>>): number {
  return b.value ?? 0;
}
export function aliased(b: Readonly<NumberBox>): number {
  return b.value;
}
export function picked(b: Pick<Box<string>, "value">): string {
  return b.value;
}
export function total(n: Readonly<Node>): number {
  return n.value + (n.next ? total(n.next) : 0);
}
export function start(): Partial<Node> {
  return { value: 1 };
}

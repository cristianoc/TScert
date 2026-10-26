// Mapped types whose value is `X[P]` at interfaces with bases: the members
// of every base, transitively and from several, each at its own modifiers,
// a member two bases declare alike once; and an interface declared in two
// parts with disjoint members, one record (rule mapped-identity).
interface Named {
  readonly name: string;
}
interface Sized {
  size?: number;
}
interface Item extends Named, Sized {
  kind: "item";
}
interface Leaf extends Item {
  depth: number;
}
interface Tagged {
  readonly name: string;
  tag: string;
}
interface Both extends Named, Tagged {}
interface Merged {
  a: number;
}
interface Merged {
  b: string;
}

export function leafName(l: Readonly<Leaf>): string {
  return l.name + l.kind + String(l.depth) + String(l.size ?? 0);
}
export function emptyLeaf(): Partial<Leaf> {
  return {};
}
export function sized(l: Required<Leaf>): number {
  return l.size + l.depth;
}
export function inherited(l: Pick<Leaf, "name" | "size">): string {
  return l.name + String(l.size ?? 0);
}
export function both(b: Partial<Both>): string {
  return (b.name ?? "") + (b.tag ?? "");
}
export function merged(m: Readonly<Merged>): string {
  return String(m.a) + m.b;
}

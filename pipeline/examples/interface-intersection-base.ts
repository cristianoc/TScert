type Left<T> = { readonly left: T };
type Right = { readonly right: string };
type Both<T> = Left<T> & Right;
interface Combined<T> extends Both<T> {
  readonly own: boolean;
}
interface InheritedOnly<T> extends Both<T> {}

export function read(x: Combined<number>): number {
  return x.left + x.right.length;
}
export function construct(): Combined<number> {
  return { left: 3, right: "yes", own: true };
}
export function inheritedOnly(x: InheritedOnly<number>): string {
  return x.right;
}

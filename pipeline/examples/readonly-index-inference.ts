type Data = null | boolean | number | string | { readonly [key: string]: Data };
function identity<T>(value: T): T {
  return value;
}
function checked<T extends Data>(value: T): T {
  return value;
}
export function field(): string {
  const a = identity("hello");
  const b = checked({ x: a });
  return b.x;
}
export function nested(): number {
  const result = checked({ child: { count: 3 }, label: "ok" });
  return result.child.count;
}

// Named members retain their contextual contracts alongside an index.
type Tagged = { readonly [key: string]: string; tag: "fixed" };
function retain<T extends Tagged>(value: T): T {
  return value;
}
export function named(): "fixed" {
  return retain({ tag: "fixed" }).tag;
}

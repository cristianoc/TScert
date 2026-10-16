// An intersection with a union holding a type parameter distributes into
// meets each known only at an instance.
interface A {
  a: number;
}
export function pick<T>(x: (T | null) & A): number {
  return x.a;
}

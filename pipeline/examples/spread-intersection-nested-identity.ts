type Id<T> = T;
export function nested(x: Id<Id<{ a: number }>> & { b: string }): {
  a: number;
  b: string;
} {
  return { ...x };
}
type Both = Id<Id<{ a: number }> & { b: string }>;
export function throughAlias(x: Id<Both>): { a: number; b: string } {
  return { ...x };
}

// Structural lookalike `{ x: number }` against `interface Box<T> { x: T }` is
// refused as ambiguous: TScert does not blindly trust TS's structural `extends` check.
interface Box<T> {
  readonly x: T;
}
type Unwrap<U> = U extends Box<infer T> ? T : never;

export function bad(v: Unwrap<{ readonly x: number }>): number {
  return v;
}

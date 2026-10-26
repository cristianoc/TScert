// A mapped type over a written key union whose value is `X[P]`: TypeScript
// copies none of X's modifiers, so `a` is required at `number | undefined`.
// The reader holds no term for that form, and refuses it.
type Source = { a?: number };
type Literal = { [P in "a"]: Source[P] };

export function read(l: Literal): number | undefined {
  return l.a;
}

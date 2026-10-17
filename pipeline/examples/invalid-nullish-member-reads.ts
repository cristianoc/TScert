// A member read past the nullish guard is the member's type: a number, no
// string.
type Box = { n: number };

export function label(b: Box | undefined): string {
  // @ts-expect-error The box may be absent.
  return b.n;
}

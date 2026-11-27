// Negative control: unfolding a transparent generic wrapper alias in
// `invariantsNamed` still requires the producer to establish the wrapped type's
// `@invariant`; returning mismatched lengths is refused and yields `NaN` under Node.

type Tagged<_Tag, T> = T;

/** @invariant this.xs.length === this.ys.length */
type EqualPair = {
  xs: number[];
  ys: number[];
};

export function badTaggedPair(): Tagged<"pair", EqualPair> {
  return { xs: [1, 2], ys: [1] };
}

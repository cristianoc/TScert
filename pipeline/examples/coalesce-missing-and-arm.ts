// A checked read written inline, `xs ?? missing()` with `missing(): never`,
// read again in the right operand of `&&` after the left operand read it so
// (pretext's `transformText`, gecko-line-breaks.ts): on the path where the
// first test found `xs` present, the second test's answer is known from
// `xs`'s slot, and its result is read at that slot's array type.
export function missing(): never {
  throw new RangeError("missing value");
}

export function frameAt(frameStarts: number[] | null, i: number): number {
  let frame = 0;
  while (
    frame < (frameStarts ?? missing()).length &&
    ((frameStarts ?? missing())[frame] ?? missing()) <= i
  )
    frame++;
  return frame;
}

export function longer(xs: number[] | null): boolean {
  return (xs ?? missing()).length > 0 && (xs ?? missing()).length > 1;
}

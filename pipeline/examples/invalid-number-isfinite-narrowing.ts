// `Number.isFinite(x)` is a Boolean of which nothing more is known: it
// does not narrow `x` to a number.
function wrong(x: string | number): number {
  return Number.isFinite(x) ? x : 0;
}

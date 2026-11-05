// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): analysis.ts#segmentAtLineBreaks.
// Refusal: reject: source incoming edge obligation: the edge does not
// establish the claims at this point (`last` at `-1 | 0 | 1 | 2`, `0 | 1 |
// 2` required).
// An equality of two names, `kind === last`, as the left operand of `&&`
// before a call: where both held, `last` equals `kind`, so it is one of
// `kind`'s values, as TypeScript narrows it. The right operand runs in a
// context that keeps `last` at its own type: the narrowing by the equality
// is not carried to it. With the call first, `gathers(kind) && kind ===
// last`, the equality is the last test and its dispatch narrows `last`.
type Kind = 0 | 1 | 2;

function kindOf(n: number): Kind {
  return n > 2 ? 2 : n > 1 ? 1 : 0;
}

function gathers(k: Kind): boolean {
  return k !== 0;
}

export function runs(n: number): number {
  let last = -1;
  let count = 0;
  for (let i = 0; i < n; i++) {
    const kind = kindOf(i);
    if (kind === last && gathers(kind)) continue;
    last = kind;
    count++;
  }
  return count;
}

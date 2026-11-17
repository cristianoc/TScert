// An index typed `SafeInt` bounded by a precondition that writes no
// `safeInteger`: the parameter's type states the index a safe integer, so
// `0 <= i && i < xs.length` means what it means with `safeInteger(i)`
// written, and the caller's tests establish it of its own `SafeInt`.
// `middle` passes a fraction to `readAt`'s `number` index (a control forges
// that parameter to `SafeInt`).

/** @requires 0 <= i && i < xs.length */
function at(xs: number[], i: SafeInt): number {
  return xs[i]!;
}

export function first(xs: number[], i: SafeInt): number {
  if (0 <= i && i < xs.length) return at(xs, i);
  return 0;
}

function readAt(xs: number[], i: number): number {
  return xs[i] ?? 0;
}

export function middle(xs: number[]): number {
  return readAt(xs, xs.length / 2);
}

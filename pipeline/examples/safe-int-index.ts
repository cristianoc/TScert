// An index typed `SafeInt` bounded by a precondition that writes no
// `safeInteger`: the parameter's type states the index a safe integer, so
// `0 <= i && i < xs.length` means what it means with `safeInteger(i)`
// written, and the caller's tests establish it of its own `SafeInt`.
// `forward` and `identity` read a `SafeInt` with no test: a precondition
// and a postcondition stating it a safe integer hold of it by its type.
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

// A `SafeInt` forwarded with no test before it: to a precondition stating
// it a safe integer, and to a postcondition stating the result one.
/** @requires safeInteger(i) */
function next(i: number): number {
  return i + 1;
}

export function forward(i: SafeInt): number {
  return next(i);
}

/** @ensures safeInteger(result) */
export function identity(i: SafeInt): SafeInt {
  return i;
}

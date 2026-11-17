// The verifier's `SafeInt` read as the safe integers: a value typed
// `SafeInt` passes to a `SafeInt` parameter and to a `number` one, a safe
// literal is one (both zeros and the extremes `±(2^53 - 1)` included), and
// an optional field holds one or `undefined`. `third` returns a fraction at
// `number` (a control forges its result to `SafeInt`).
function keep(i: SafeInt): SafeInt {
  return i;
}

export function pass(i: SafeInt): SafeInt {
  return keep(i);
}

export function widen(i: SafeInt): number {
  return i;
}

export function literals(): SafeInt[] {
  return [0, -0, 42, -7, 9007199254740991, -9007199254740991];
}

export type Entry = { readonly size?: SafeInt };

export function make(n: SafeInt): Entry {
  return { size: n };
}

export function sizeOf(e: Entry): SafeInt | undefined {
  return e.size;
}

export function third(x: number): number {
  return x / 3;
}

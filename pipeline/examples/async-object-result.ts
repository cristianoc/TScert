// An async function settling to a fresh object literal: JavaScript would
// adopt it if it had a `then`, its own or one on its prototype. The literal
// owns exactly the keys it writes, and its prototype is the standard
// `Object.prototype`, which has no `then`, so its promise settles to it.
export async function make(): Promise<{ n: number }> {
  return { n: 1 };
}

// Each arm of a conditional, and a literal holding another.
export async function pick(b: boolean): Promise<{ n: number } | { s: string; inner: { n: number } }> {
  if (b) return { n: 2 };
  return b ? { n: 3 } : { s: "x", inner: { n: 4 } };
}

// A literal whose `then` is a primitive, which the resolution reads and does
// not call.
export async function primitive(): Promise<{ then: number }> {
  return { then: 5 };
}

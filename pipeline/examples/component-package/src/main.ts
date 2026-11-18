// The package's `.` export (component-package/package.json). Its handle's
// record holds fields its type does not show; a boxed record has a writable
// descendant; a counter's closure escapes through its result, and a thunk
// through an argument of the caller's code.
/** A handle: its records hold `widths` and `cache` beside `size`. */
export type Handle = { readonly size: number };
/** A record whose box, and the array in it, the caller may change. */
export type Boxed = { readonly box: { xs: number[] } };

export function prepare(n: number): Handle {
  return { size: n, widths: [n], cache: [] };
}

export function boxed(n: number): Boxed {
  return { box: { xs: [n] } };
}

export function counter(start: number): () => number {
  return (): number => start;
}

export function later(run: (f: () => number) => void): void {
  run((): number => 1);
}

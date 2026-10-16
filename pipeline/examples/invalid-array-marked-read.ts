// A marked tuple's marker reads as `true`, not as a number.
declare const marker: unique symbol;
type Marked = { readonly [marker]: true };
export function wrong(xs: [number, number] & Marked): number {
  // @ts-expect-error: the marker is `true`
  return xs[marker];
}

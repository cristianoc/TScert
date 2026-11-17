// A mapped type over `SafeInt`: TypeScript computes its keys at `number`,
// which would widen the keys it states to every number, so the form is
// refused at the source boundary.
type ByIndex = { [K in SafeInt]: string };

export function get(r: ByIndex, k: number): string | undefined {
  return r[k];
}

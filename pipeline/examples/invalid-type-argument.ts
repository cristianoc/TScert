// An explicit type argument fixes the instance a generic method is called
// at: `reduce<number | null | string>` offers its callback strings, which
// this accumulator does not take. Inferred, the instance would be
// `number | null`, which fits.
export function minus(xs: [number, number][]): number | null | string {
  const acc = (p: number | null, c: [number, number]) => {
    return p !== null ? p - c[1] : c[1];
  };
  return xs.reduce<number | null | string>(acc, null);
}

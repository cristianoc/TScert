// The inferred closure result and explicit reduce instance are checked independently.
export function minus(xs: number[]): number {
  const acc = (p: number | null, c: number) => {
    return p !== null ? p - c : c;
  };
  return xs.reduce<number | null>(acc, null) ?? 0;
}

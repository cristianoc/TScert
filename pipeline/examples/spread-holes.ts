// TypeScript accepts this, but the write leaves a hole at index 1, and
// spreading would pass it as undefined, violating boolean[]. This element contract forbids holes:
// the write is refused, so no spread ever meets a hole.
function spreadsArray(seed: boolean): boolean[] {
  const values: boolean[] = [seed];
  values[2] = seed;
  const collect = (...rest: boolean[]): boolean[] => rest;
  return collect(...values);
}

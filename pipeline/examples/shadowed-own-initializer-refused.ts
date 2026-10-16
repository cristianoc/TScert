// A declaration's own initializer naming it reads its binding before it is
// initialized (JavaScript throws there), not the module constant.
const seed: number = 1;
export function own(): number {
  const seed = seed + 1;
  return seed;
}

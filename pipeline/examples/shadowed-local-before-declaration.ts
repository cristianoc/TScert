// A read of a shadowing local above its declaration runs before the local is
// initialized: JavaScript throws there, and the module constant of its name
// is not what it reads. Refused by the parser.
const seed: number = 1;
export function laterStatement(): number {
  const first = seed;
  const seed = 2;
  return first;
}

// The type TypeScript infers for an object literal's field is its widened
// type: `x` is a number, not a string.
const origin = { x: 0 };
export function copy(p: typeof origin): string {
  return p.x;
}

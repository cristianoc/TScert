// A function reads an unannotated module constant at the type the module's
// initialization claims for its initializer and checks it holds: TypeScript's
// declared type for a `const`, a literal kept as its literal type.
const on = true;
const count = 1;
const origin = { x: 0, y: 0 };
export function read(): boolean {
  return on;
}
export function literal(): 0 | 1 {
  return count;
}
export function field(): number {
  return origin.x;
}

// An unannotated module constant is read at its initializer's type, `2`,
// which is not the function's `0 | 1`.
const two = 2;
export function literal(): 0 | 1 {
  return two;
}

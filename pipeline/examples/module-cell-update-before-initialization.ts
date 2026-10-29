// The initialization calls a function updating a module cell before its
// declaration runs: the update's checked access throws a ReferenceError
// (run under Node), which the model states.
function bump(): number {
  return ++count;
}
const first: number = bump();
let count: number = 0;

export function total(): number {
  return count + first;
}

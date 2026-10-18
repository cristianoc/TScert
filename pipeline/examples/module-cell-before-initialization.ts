// The initialization calls a function reading a module cell before its
// declaration runs: the checked access throws a ReferenceError (run under
// Node), which the model states.
function read(): number {
  return x;
}
const y: number = read();
let x: number = 1;

export function sum(): number {
  return x + y;
}

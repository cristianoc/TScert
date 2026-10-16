// The module's top-level code runs once, in order, after its function
// declarations exist. A function reads a module constant at its annotation,
// and initialization may call a function once what it reads holds a value.
const on: boolean = true;
function read(): boolean {
  return on;
}
const copy: boolean = read();
read();
export function again(x: boolean): boolean {
  return copy;
}

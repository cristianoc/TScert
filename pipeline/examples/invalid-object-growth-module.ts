// A module constant is a module value the module's functions read: a write
// adding a key to its object is refused.
const o = {};
o.x = 1;
export function read(): {} {
  return o;
}

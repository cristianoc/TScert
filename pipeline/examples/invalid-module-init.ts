// A module constant's initializer must meet its annotation: the functions
// that read it assume it.
const flag: boolean = null;
export function get(): boolean {
  return flag;
}

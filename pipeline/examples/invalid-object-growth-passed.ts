// A callee may keep the object it was passed: a later write that would add a
// key is refused.
declare function keep(o: {}): void;
export function grow(): { x: number } {
  const o = {};
  keep(o);
  o.x = 1;
  return o;
}

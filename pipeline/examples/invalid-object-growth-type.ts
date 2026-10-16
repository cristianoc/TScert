// The added key holds a number: the object is no `{ x: string }`.
export function grow(): { x: string } {
  const o = {};
  o.x = 5;
  return o;
}

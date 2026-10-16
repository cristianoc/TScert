// A write in a loop its object's declaration does not enclose runs on an
// object an earlier round may have let escape: refused.
declare function keep(o: {}): void;
export function grow(n: number): { x: number } {
  const o = {};
  for (let i = 0; i < n; i++) {
    o.x = i;
    keep(o);
  }
  return { x: 0 };
}

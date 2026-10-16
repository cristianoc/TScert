// A numeric property name is the key `ToString` of its value: `0x10`, `16`
// and `1_6` name the one key "16", in types, mapped types and object
// literals.
type Pair = { [P in 0 | 1]: string };
function hex(x: { 0x10: string; 1e3: number }): { 16: string; 1000: number } {
  return x;
}
function literal(): { 0: number; 1.5: string } {
  return { 0: 1, 1.5: "a" };
}
function pair(): Pair {
  return { 0: "a", 1: "b" };
}
export function use(): number {
  return hex({ 16: "x", 1000: 2 })[1000] + literal()[0] + pair()[1].length;
}

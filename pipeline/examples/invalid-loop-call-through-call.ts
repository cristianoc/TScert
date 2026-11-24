// A loop calling a function through `.call` may change a module cell:
// `raise.call(undefined)` sets `flag` (run under Node: `g(1)` returns true
// at the declared result `false`).
let flag: boolean = false;
function raise(): void {
  flag = true;
}
export function g(n: number): false {
  if (flag) return false;
  for (let i = 0; i < n; i++) raise.call(undefined);
  return flag;
}

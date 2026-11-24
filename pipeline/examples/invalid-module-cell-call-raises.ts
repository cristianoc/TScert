// A call may change a module cell: TypeScript keeps `flag` narrowed to
// `false` across `raise()`, which sets it (run under Node:
// `moduleClosed()` returns true at the declared result `false`).
let flag: boolean = false;
function raise(): void {
  flag = true;
}
export function moduleClosed(): false {
  if (flag) return false;
  raise();
  return flag;
}

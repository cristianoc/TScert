// A call may change a cell's contents: TypeScript keeps `refused` and
// `flag` narrowed to `false` across the calls that assign them, so each
// function returns `true` at its declared result `false` (run under Node:
// `closed(["x"])` and `moduleClosed()` both return true).
let flag: boolean = false;
function raise(): void {
  flag = true;
}
export function closed(xs: string[]): false {
  let refused = false;
  const visit = (s: string): void => {
    if (s === "x") refused = true;
  };
  for (const x of xs) visit(x);
  return refused;
}
export function moduleClosed(): false {
  if (flag) return false;
  raise();
  return flag;
}

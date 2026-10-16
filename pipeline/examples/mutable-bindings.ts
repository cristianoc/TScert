// Mutable bindings as TypeScript declares them. An unannotated `let` stores
// its initializer's widened type; an assigned parameter is a cell at its
// annotation; `let x: T;` is a cell of `T | undefined` holding `undefined`,
// read at `T` where every path to the read has assigned it.
function counter(seed: number): number {
  let total = 0;
  total = total + seed;
  let point = { x: 1, y: "a" };
  point = { x: 2, y: "b" };
  return total + point.x;
}
function captured(): () => string {
  let greeting = "hello";
  return () => greeting;
}
function reassignedParameter(n: number, reset: boolean): number {
  if (reset) {
    n = 0;
  }
  return n;
}
function assignedOnEveryPath(flag: boolean): string {
  let label: string;
  if (flag) {
    label = "on";
  } else {
    label = "off";
  }
  return label;
}
function assignedThenRead(): number {
  let x: number;
  x = 2;
  return x + 1;
}
function readAfterGuard(cond: boolean): number {
  let x: number | undefined;
  if (cond) x = 1;
  if (x === undefined) return 0;
  return x;
}
function lastInBlock(flag: boolean): number {
  while (flag) {
    let step = 1;
  }
  return 0;
}

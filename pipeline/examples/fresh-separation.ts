/**
 * A cell a function allocates (a `let` a closure captures) sits at a location
 * no older object has: a write to it keeps what is known about a parameter's
 * field. The allocation states the separation once; loop iterations, joins,
 * calls and a handler's edge keep it.
 */
function helper(): number {
  return 1;
}
/** A cell allocated by each iteration, written: the parameter's field keeps its test. */
export function loopCells(x: { value: number | null }, n: number): number {
  let total = 0;
  for (let i = 0; i < n; i++) {
    if (x.value === null) return total;
    let count = 0;
    const read = (): number => count;
    const v = (count = x.value);
    total = total + x.value + v + read();
  }
  return total;
}
/** A cell initialized by a join of two values, written. */
export function joinedCell(x: { value: number | null }, b: boolean): number {
  if (x.value === null) return 0;
  let c = b ? 1 : 2;
  const read = (): number => c;
  const v = (c = x.value);
  return x.value + v + read();
}
/** A call between the cell's allocation and its write keeps the separation. */
export function callCell(x: { value: number | null }): number {
  let c = 1;
  const read = (): number => c;
  helper();
  if (x.value === null) return 0;
  const v = (c = x.value);
  return x.value + v + read();
}
/** A handler keeps the separation established before the throwing call. */
export function handlerCell(
  x: { value: number | null },
  f: () => number,
): number {
  let c = 1;
  const read = (): number => c;
  try {
    return f();
  } catch {
    if (x.value === null) return 0;
    const v = (c = x.value);
    return x.value + v + read();
  }
}

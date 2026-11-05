// `new Array<T>(n).fill(v)`: the construct written directly as the receiver
// of `fill` of one argument is a fresh dense `T[]`, every index holding `v`
// (SOURCE-CONTRACTS.md, "`new Array` filled at once"). `n` is evaluated, then
// the length is checked (a RangeError where `n` is no array length), then
// `v`, and the array no code reached before is returned.

// Pretext's shape: a table made on first need, filled with `null`, then
// given an element of the wider type. An existing table skips the
// construct and its value.
export function record(
  table: (number[] | null)[] | null,
  size: number,
  units: number[],
): (number[] | null)[] {
  let slots = table;
  if (units.length > 0)
    (slots ??= new Array<number[] | null>(size).fill(null)).push(units);
  return slots ?? [];
}

// A value computed by a call, evaluated after the length's check.
let calls: number = 0;
function next(): number {
  calls += 1;
  return calls;
}
export function counted(n: number): number[] {
  return new Array<number>(n).fill(next());
}

// An object fill: every index holds the same object, which a write through
// one element changes for all.
export function shared(n: number): { count: number }[] {
  const cell = { count: 0 };
  const cells = new Array<{ count: number }>(n).fill(cell);
  for (const c of cells) c.count += 1;
  return cells;
}

// A dense result: iteration reads every element as a number.
export function total(n: number): number {
  let sum = 0;
  for (const x of new Array<number>(n).fill(2)) sum += x.toFixed(0).length;
  return sum;
}

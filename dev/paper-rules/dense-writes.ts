// Direct in-bounds dense-array writes (`Dense-Elem-Write`):
// an element write `arr[i] = v` on a `Dense<T[]>` with `0 <= i < arr.length`
// certifies `Effects<{ "arr[#]": "any" }, void>` without `arr[*]: grow`;
// appending (`i === arr.length`), non-`Dense` arrays, or unbounded indices
// are refused by `denseWriteStep`.

type Footprint = {
  [location: string]:
    | "keep"
    | "init"
    | "scalar"
    | "extend"
    | "grow"
    | "any"
    | true;
};
type Effects<P extends Footprint, T> = T;

/**
 * @requires safeInteger(count) && 0 <= count
 * @ensures result.length === count
 */
function zeros(count: number): Modifies<{}, Fresh<Dense<number[]>>> {
  const out: Dense<number[]> = [];
  /** @invariant safeInteger(count) && safeInteger(i) && 0 <= i && i <= count && out.length === i */
  for (let i = 0; i < count; i++) out.push(0);
  return out;
}

// Positive: in-bounds write on `Dense<number[]>` satisfies `arr[#]: any`
// (spines kept).
/**
 * @requires safeInteger(i) && 0 <= i && i < arr.length
 */
export function writeDenseInBounds(
  arr: Dense<number[]>,
  i: number,
  v: number,
): Effects<{ "arr[#]": "any" }, void> {
  arr[i] = v;
}

// Positive: nullable `Dense<number[]> | null` initialized with `??= zeros(n)`
// satisfies `arr[#]: any` on the in-bounds write.
/**
 * @requires safeInteger(n) && safeInteger(i) && 0 <= i && i < n
 * @requires arr === null || n <= arr.length
 * @ensures result.length >= n
 */
export function writeDenseNullable(
  arr: Dense<number[]> | null,
  n: number,
  i: number,
  v: number,
): Effects<{ "arr[#]": "any" }, Dense<number[]>> {
  arr ??= zeros(n);
  arr[i] = v;
  return arr;
}

// Positive: caller of `writeDenseInBounds` preserves unrelated array lengths
// and quantified invariants across the `arr[#]: any` effect.
/**
 * @requires safeInteger(i) && 0 <= i && i < xs.length && i < ys.length
 * @requires forall k in rows: rows[k] === null || 1 <= rows[k].length
 * @ensures forall k in rows: rows[k] === null || 1 <= rows[k].length
 */
export function callerPreservesLengths(
  xs: Dense<number[]>,
  ys: number[],
  rows: (number[] | null)[],
  i: number,
): number {
  writeDenseInBounds(xs, i, 7);
  return ys[i]!;
}

// Negative: appending `arr[arr.length] = v` on `Dense<number[]>` grows the
// spine, violating `Effects<{ "arr[#]": "any" }, void>`.
export function writeDenseAppend(
  arr: Dense<number[]>,
  v: number,
): Effects<{ "arr[#]": "any" }, void> {
  arr[arr.length] = v;
}

// Negative: non-`Dense` `number[]` may have a hole at `i < arr.length`, so
// writing `arr[i] = v` allocates a cell and mutates the spine.
/**
 * @requires safeInteger(i) && 0 <= i && i < arr.length
 */
export function writeNonDenseInBounds(
  arr: number[],
  i: number,
  v: number,
): Effects<{ "arr[#]": "any" }, void> {
  arr[i] = v;
}

// Negative: `i <= arr.length` permits appending at `i === arr.length`, so
// `denseWriteStep` refuses `Effects<{ "arr[#]": "any" }, void>`.
/**
 * @requires safeInteger(i) && 0 <= i && i <= arr.length
 */
export function writeDenseAtLength(
  arr: Dense<number[]>,
  i: number,
  v: number,
): Effects<{ "arr[#]": "any" }, void> {
  arr[i] = v;
}

// Negative: a nested function claiming `Effects<{ "a[#]": "any" }, void>`
// around `a[a.length] = x` has no top-level Lean unit to certify
// `denseWriteStep`, so calling it must be refused.
export function nestedDenseAppendOuter(
  arr: Dense<number[]>,
  v: number,
): Effects<{ "arr[#]": "any" }, void> {
  function inner(a: Dense<number[]>, x: number): Effects<{ "a[#]": "any" }, void> {
    a[a.length] = x;
  }
  inner(arr, v);
}

/**
 * @requires safeInteger(i) && 0 <= i && i < xs.length
 */
export function callerOfNestedDenseAppend(xs: Dense<number[]>, i: number): number {
  nestedDenseAppendOuter(xs, 1);
  return xs[i]!;
}

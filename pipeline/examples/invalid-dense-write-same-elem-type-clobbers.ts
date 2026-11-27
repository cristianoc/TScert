// Two plain arrays with the same element type (`Dense<number[]>` and `number[]`)
// may alias when no `!==` / `apart` fact separates them. Writing `widths[i] = 0`
// can clobber `forall k in targets: 1 <= targets[k]`, causing `out[targets[i] - 1]`
// to read `out[-1]` (`undefined`) and return `NaN` at runtime.

/**
 * @requires safeInteger(i) && 0 <= i && i < widths.length && i < targets.length && 1 <= out.length
 * @requires forall k in targets: 1 <= targets[k] && targets[k] <= out.length
 */
export function clobberAndRead(
  widths: Dense<number[]>,
  targets: SafeInt[],
  out: number[],
  i: number,
): number {
  widths[i] = 0;
  const t = targets[i]!;
  return out[t - 1]! + 1;
}

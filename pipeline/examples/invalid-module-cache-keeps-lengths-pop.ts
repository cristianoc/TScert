// A module cache that is an array the caller counts: `count` pops it, so
// the caller's bound does not survive the call. Under Node, `total()` with
// `cache = [1, 2, 3]` reads `cache[1]` of `[1]` after two pops, `undefined`
// at `number`, and answers `NaN`.

const cache: number[] = [1, 2, 3];

function count(): number {
  cache.pop();
  return cache.length;
}

export function total(): number {
  let t = 0;
  for (let i = 0; i < cache.length; i++) t += count() + cache[i]!;
  return t;
}

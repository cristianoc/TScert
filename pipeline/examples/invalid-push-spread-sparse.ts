// A `map` whose callback pops its array promises a sparse result: a spread
// of it passes a hole as `undefined`, which `number[]` excludes.
export function wrong(src: number[]): number {
  const xs: number[] = [];
  const ys = src.map((v) => {
    src.pop();
    return v;
  });
  xs.push(...ys);
  let last = 0;
  for (const x of xs) last = x;
  return last;
}

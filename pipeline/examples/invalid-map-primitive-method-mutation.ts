// A callback calling a string's method and an array's mutator: `pop`
// shrinks the source, so the callback is not heap-preserving, `map` takes its
// unrestricted overload and its result may hold a hole, which the loop reads
// as `undefined`.
export function wrong(xs: string[]): string {
  const ys = xs.map((x: string): string => {
    xs.pop();
    return x.trim();
  });
  let last = "";
  for (const y of ys) last = y;
  return last;
}

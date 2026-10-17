// A variable holding a fresh array and then the mapped one: `pop` through it
// changes the mapped array's store, so the result has holes.
export function drained(xs: string[]): string[] {
  return xs.map((x) => {
    let a = x.split("");
    a = xs;
    a.pop();
    return x;
  });
}

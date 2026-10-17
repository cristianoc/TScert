// A callback with a local `let` it updates: invisible to the caller.
export function lengths(xs: readonly string[]): number[] {
  return xs.map((s: string): number => {
    let n = 0;
    for (let i = 0; i < s.length; i++) n = n + 1;
    return n;
  });
}

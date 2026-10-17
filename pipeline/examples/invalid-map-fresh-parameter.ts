// A helper popping its parameter: the parameter's store is the caller's, so
// the helper is bounded by `pop`'s signature without the exception, and the
// callback calling it at the mapped array gives a result with holes.
function drop(a: string[]): void {
  a.pop();
}

export function drained(xs: string[]): string[] {
  return xs.map((x) => {
    drop(xs);
    return x;
  });
}

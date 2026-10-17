// A callee that shrinks the array `map` visits before it throws: a callback
// catching the throw continues with a shorter array, and the result has a
// hole below its length.
function popThen(xs: number[]): number {
  xs.pop();
  throw Error("popped");
}
export function wrong(xs: number[]): number[] {
  return xs.map((x: number): number => {
    try {
      return popThen(xs);
    } catch {
      return x;
    }
  });
}

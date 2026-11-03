// Inserting fewer values than splice removes shrinks the mapped receiver.
export function broken(xs: string[]): string[] {
  return xs.map((x) => {
    xs.splice(0, xs.length, x);
    return x;
  });
}

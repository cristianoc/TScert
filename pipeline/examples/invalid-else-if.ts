// The last arm of an `else if` chain is reached only where every test failed:
// here `x` is null there.
function narrowed(x: number | null, y: boolean): number {
  if (y) return 1;
  else if (x !== null) return 2;
  else return x;
}

// The block's `seed` ends with its block: the return reads the function's
// string, not the block's number nor the module's.
const seed: number = 1;
export function bad(): number {
  const seed = "local";
  {
    const seed = 2;
    void seed;
  }
  return seed;
}

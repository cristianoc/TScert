// `throw new Error(m)`: the overlay's statement of `new Error`, then a throw.
function positive(x: number): number {
  if (x < 0) {
    throw new Error("negative");
  }
  return x;
}

function describe(f: () => number): string {
  try {
    f();
    return "ok";
  } catch (e) {
    throw new Error("failed");
  }
}

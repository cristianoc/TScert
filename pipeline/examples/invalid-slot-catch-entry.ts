// A throw from the call leaves the try with `y` at "b": the catch is entered
// with each value a write before a throwing step left there, and returns "b"
// when `mayThrow` throws.
export function midTry(a: "a", b: "b", mayThrow: () => void): "a" {
  let y: "a" | "b" = a;
  try {
    y = b;
    mayThrow();
    y = a;
  } catch {
    return y as "a";
  }
  return y;
}

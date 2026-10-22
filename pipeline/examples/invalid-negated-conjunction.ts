// Where `!(a && b)` holds, either test may have failed: the first one's
// field keeps what it tested.
type Name = { name: "a" | "b" | "c" | "d" };

export function wrong(k: Name, n: number): "b" | "c" | "d" | "x" {
  if (!(k.name === "a" && n === 1)) {
    // @ts-expect-error k.name may be "a" here
    return k.name;
  }
  return "x";
}

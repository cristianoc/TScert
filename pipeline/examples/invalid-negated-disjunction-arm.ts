// The conditional's false arm is where `!(a || b)` fails: one of the tests
// held.
type Name = { name: "a" | "b" | "c" | "d" };

export function wrong(k: Name): "c" | "d" | "x" {
  // @ts-expect-error the false arm holds "a" | "b"
  return !(k.name === "a" || k.name === "b") ? "x" : k.name;
}

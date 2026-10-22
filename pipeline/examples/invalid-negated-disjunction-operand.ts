// The test's second operand writes the field the first one tested.
type Name = { name: "a" | "b" | "c" | "d" };

function touch(k: Name): boolean {
  k.name = "a";
  return false;
}

export function wrong(k: Name): "b" | "c" | "d" | "x" {
  if (!(k.name === "a" || touch(k))) return k.name;
  return "x";
}

// A call between the test and the read writes the tested field.
type Name = { name: "a" | "b" | "c" | "d" };

function reset(k: Name): void {
  k.name = "a";
}

export function wrong(k: Name): "c" | "d" | "x" {
  if (!(k.name === "a" || k.name === "b")) {
    reset(k);
    return k.name;
  }
  return "x";
}

// A getter answers each read anew: the tests' reads and the later one may
// differ. Accessors are outside the fragment.
class Flip {
  n: number = 0;
  get name(): "a" | "b" | "c" | "d" {
    this.n++;
    return this.n === 1 ? "c" : "a";
  }
}

export function wrong(k: Flip): "c" | "d" | "x" {
  if (!(k.name === "a" || k.name === "b")) return k.name;
  return "x";
}

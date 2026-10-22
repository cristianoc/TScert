// A getter answers each read anew: the test's read and the later one may
// differ, where TypeScript reads the second at the first's answer.
// Accessors are outside the fragment.
class Flip {
  n: number = 0;
  get k(): "d" | "e" {
    this.n++;
    return this.n === 1 ? "d" : "e";
  }
}

export function wrong(b: Flip | undefined): "d" {
  return b?.k === "d" ? b.k : "d";
}

// A class with a static `toString` is a function owning one: a function's
// `toString` lookup finds it before `Function.prototype`'s, and runs it.
// Here it writes the caller's heap, which the native's empty footprint does
// not admit. The class is refused (SOURCE-CONTRACTS.md,
// "Function.prototype.toString"). Under Node, `runs(Shadow, "t")` returns
// `true` and leaves `state.n` at `"written"`.
export const state: { n: string } = { n: "" };

export class Shadow {
  static toString(): string {
    state.n = "written";
    return "t";
  }
}

export function runs(value: unknown, text: string): boolean {
  return typeof value === "function" && value.toString() === text;
}

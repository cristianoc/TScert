// A negation of `||` or `&&` over tests, in a condition, a conditional and
// a closure: where the first test failed, the field the second one reads is
// what that failure left, and each branch is what the negation answers.
type Name = { name: "a" | "b" | "c" | "d" };
type Term =
  | { k: "atom"; name: "string" | "number" | "symbol" | "never" }
  | { k: "literal"; name: "string" | "number" | "bigint" };

export function rest(k: Name): "c" | "d" | "x" {
  if (!(k.name === "a" || k.name === "b")) return k.name;
  return "x";
}

export function tested(k: Name): "a" | "b" | "x" {
  if (!(k.name === "a" || k.name === "b")) return "x";
  return k.name;
}

export function conjunction(k: Name): "b" | "c" | "x" {
  if (!(k.name !== "b" && k.name !== "c")) return k.name;
  return "x";
}

export function other(k: Name, n: number): "b" | "x" {
  if (!(k.name !== "b" || n !== 1)) return k.name;
  return "x";
}

export function exact(k: { name: "a" | "b" }, n: number): 1 {
  if (!(k.name !== "b" || n !== 1)) return n;
  return 1;
}

export function doubled(k: Name): "a" | "b" | "x" {
  if (!!(k.name === "a" || k.name === "b")) return k.name;
  return "x";
}

export function nested(k: Name): "d" | "x" {
  if (!(k.name === "a" || !(k.name !== "b" && k.name !== "c"))) return k.name;
  return "x";
}

export function chosen(k: Name): "c" | "d" | "x" {
  return !(k.name === "a" || k.name === "b") ? k.name : "x";
}

export function chosenOther(k: Name, n: number): "b" | "x" {
  return !(k.name !== "b" || n !== 1) ? k.name : "x";
}

export function operand(k: Name, more: boolean): boolean {
  return !(k.name === "a" || k.name === "b") && more;
}

export function unusual(keys: readonly Term[]): boolean {
  return keys.some(
    (k) =>
      !(
        k.k === "atom" &&
        (k.name === "string" || k.name === "number" || k.name === "symbol")
      ) && !(k.k === "literal" && (k.name === "string" || k.name === "number")),
  );
}

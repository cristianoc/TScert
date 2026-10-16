// A constant made by `Symbol.for("k")` holds the registry's symbol for "k":
// constants made from different strings name different keys.
const left: unique symbol = Symbol.for("app.left");
const right: unique symbol = Symbol.for("app.right");
export function read(o: { [left]: number; [right]: string }): number {
  return o[left] + o[right].length;
}

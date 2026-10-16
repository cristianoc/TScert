// `keyof` of a type with a member keyed by a `unique symbol` is the union of
// its keys, the symbol's own type among them: a tuple's and a string's
// `[Symbol.iterator]`, a promise's `[Symbol.toStringTag]`, a program's own
// `unique symbol` constant. Values of the string and number keys meet it,
// and a key is compared with a literal as any primitive is.
const tag: unique symbol = Symbol();
interface Tagged {
  name: string;
  [tag]: number;
}
const zero: keyof [number] = 0;
const one: keyof [number] = 1;
const zeroKey: keyof [number] = "0";
const length: keyof [number] = "length";
const anyIndex: keyof "a" = 99;
const method: keyof string = "charAt";
function promiseKey(k: "then" | "catch" | "finally"): keyof Promise<number> {
  return k;
}
function isThen(k: keyof Promise<number>): boolean {
  return k === "then";
}
function taggedName(): keyof Tagged {
  return "name";
}
function nameOf(k: keyof Tagged): string {
  return k === "name" ? "name" : "symbol";
}

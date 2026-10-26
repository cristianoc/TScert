// A key a function owns or inherits from `Function.prototype` (`name`,
// `prototype`, `call`, `apply`, `bind`, `arguments`, `caller`) tested on an
// operand no arm of which is a function: an object without call code owns
// such a key as a field or inherits it from a class's prototype object, as
// the model holds it. A failed test drops the arms owning the key, a `typeof`
// test finding an object drops a function arm, and a passed test on a class
// instance reads the inherited method.
type Binder = { call: string; bound: number } | { kind: "plain"; size: number };

export function sizeOf(v: Binder): number {
  return "call" in v ? 0 : v.size;
}

export function anyOf(
  v: Binder,
  k: "call" | "apply" | "bind" | "prototype",
): boolean {
  return k in v || "arguments" in v || "caller" in v;
}

export function bound(x: { bind: string } | (() => number)): string {
  return typeof x === "object" && "bind" in x ? x.bind : "";
}

class Caller {
  call(): number {
    return 1;
  }
}

export function inherited(c: Caller): boolean {
  return "call" in c;
}

export function count(vs: Binder[], k: "call" | "bind"): number {
  return vs.filter((v) => k in v).length;
}

export function read(c: Caller): number {
  return "call" in c ? c.call() : 0;
}

export function named(x: { name: string } | (() => number)): string {
  return typeof x === "object" && "name" in x ? x.name : "";
}

export function labelled(
  v: { name: string; size: number } | { size: number },
): number {
  return "name" in v ? 1 : v.size;
}

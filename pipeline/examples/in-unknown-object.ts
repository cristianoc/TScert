// `unknown` is the union of the kinds of a JavaScript value: null,
// undefined, a Boolean, a number, a string, a bigint, a symbol, an object
// without call code, and one with call code. A test keeps the kinds it does
// not contradict, so after `typeof x === "object"` and `x !== null` the
// value is an object without call code, on which `in` does not throw.
export function anything(x: unknown): boolean {
  return typeof x === "object" && x !== null && "a" in x;
}

// A falsy value is no object: `!x ||` drops null and undefined first.
export function closable(x: unknown): boolean {
  if (!x || typeof x !== "object") return false;
  return "close" in x;
}

// A caught value, tested for a key: an object holds no function's `name`.
export function named(f: () => void): boolean {
  try {
    f();
    return false;
  } catch (e) {
    return e != null && typeof e === "object" && "name" in e;
  }
}

// The kinds a chain of tests leaves, each at its own type.
export function kind(x: unknown): string {
  if (x == null) return "nullish";
  if (typeof x === "function") return "function";
  if (typeof x !== "object") return "primitive";
  return "code" in x ? "coded" : "object";
}

// `typeof x === "function"` leaves a function: one invocable, or a class.
export function callable(x: unknown): unknown {
  return typeof x === "function" ? x : null;
}

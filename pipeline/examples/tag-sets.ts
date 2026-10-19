// Tag sets: a union of two or more literals of one primitive is one set,
// which tests slice element by element, keys enumerate, meets intersect and
// coverage reads beside the union's other clauses.
type Op = "add" | "sub" | "mul";

// A program alias of a literal union, narrowed by equality on both edges to
// one element and to the rest.
export function apply(op: Op, a: number, b: number): number {
  if (op === "add") return a + b;
  if (op === "sub") return a - b;
  const m: "mul" = op;
  return m === "mul" ? a * b : 0;
}

// A mixed union: literals of two primitives beside `null`, narrowed by
// `typeof` and by equality.
export function mixed(x: 1 | 2 | "a" | "b" | null): number {
  if (x === null) return 0;
  if (typeof x === "string") {
    const s: "a" | "b" = x;
    return s.length;
  }
  const n: 1 | 2 = x;
  return n;
}

// Both edges of truthiness: the zeros are falsy, the others truthy.
export function truthy(x: 0 | 1 | 2, s: "" | "a" | "b"): number {
  let r = 0;
  if (x) {
    const y: 1 | 2 = x;
    r = y;
  } else {
    const z: 0 = x;
    r = z;
  }
  if (s) {
    const t: "a" | "b" = s;
    r = r + t.length;
  } else {
    const e: "" = s;
    r = r + e.length;
  }
  return r;
}

// Slices to one element and to none; the zero test keeps both zeros.
export function slices(x: 0 | 1 | 2): number {
  if (x === 0) {
    const z: 0 = x;
    return z;
  }
  if (x === 1) return 1;
  const two: 2 = x;
  return two;
}

// A computed key at a set reads the member each element names.
export function pick(k: "f" | "g" | "h", o: { f: number; g: number; h: number }): number {
  return o[k];
}

// The meet of two sets, and of a set with its primitive.
export function meets(x: (1 | 2 | 3) & (2 | 3 | 4), y: (1 | 2) & number): number {
  const m: 2 | 3 = x;
  const n: 1 | 2 = y;
  return m + n;
}

// A set covered by a wider union: its elements by its set and a family.
export function covered(x: 1 | 2 | 3): 1 | 2 | 3 | 4 | string {
  return x;
}

// Guards called through an object: an interface's method guard and method
// assertion function, a class's method guard checked at its body, and guards
// held in an object's fields; each call narrows its actual.
export interface Checker {
  isWord(x: unknown): x is string;
  word(x: unknown): asserts x is string;
}

export function size(c: Checker, v: unknown): number {
  if (c.isWord(v)) return v.length;
  return 0;
}

export function size2(c: Checker, v: unknown): number {
  return c.isWord(v) ? v.length : 0;
}

export function size3(c: Checker, v: unknown): number {
  c.word(v);
  return v.length;
}

export class Box {
  isWord(x: unknown): x is string {
    return typeof x === "string";
  }
}

export function size4(b: Box, v: unknown): number {
  if (b.isWord(v)) return v.length;
  return 0;
}

const checks: {
  isWord: (x: unknown) => x is string;
  word: (x: unknown) => asserts x is string;
} = {
  isWord: (x: unknown): x is string => typeof x === "string",
  word: (x: unknown): asserts x is string => {
    if (typeof x !== "string") throw Error("not a string");
  },
};

export function size5(v: unknown): number {
  return checks.isWord(v) ? v.length : 0;
}

export function size6(v: unknown): number {
  checks.word(v);
  return v.length;
}

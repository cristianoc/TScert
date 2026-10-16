// Strict equality with a singleton of every primitive kind is a tag test,
// which narrows the other operand on both edges. Without a singleton, `===`
// compares two primitives, or an object with a field and any value, exactly;
// `== null` is the nullish test.
function stringTag(x: "a" | "b" | null): number {
  if (x === "a") {
    const a: "a" = x;
    return 1;
  }
  if (x !== null) {
    const b: "b" = x;
    return 2;
  }
  return 0;
}

function booleanTag(b: boolean | undefined): number {
  if (b === true) {
    const t: true = b;
    return 1;
  }
  if (false === b) {
    const f: false = b;
    return 0;
  }
  const u: undefined = b;
  return -1;
}

function bigintTag(n: 1n | 2n): 1n | 2n {
  if (n === 1n) {
    const one: 1n = n;
    return one;
  }
  const two: 2n = n;
  return two;
}

function namedSingleton(x: string | null, none: null): string {
  if (x === none) {
    return "";
  }
  return x;
}

function primitives(
  x: number,
  y: string,
  z: 0 | 1,
  w: 1 | 2,
  u: unknown,
): boolean {
  const a: boolean = x === y;
  const b: boolean = z === w;
  const c: boolean = u !== x;
  return a || b || c;
}

class Cat {
  meow: string = "";
}
class Dog {
  bark: string = "";
}

function identity(c: Cat, d: Dog, f: () => number): boolean {
  const same: boolean = c === d;
  return same || f === c;
}

function looseNull(x: string | null | undefined): string {
  if (x == null) {
    return "";
  }
  return x;
}

function looseUnequal(x: number | undefined): number {
  if (undefined != x) {
    return x;
  }
  return 0;
}

// Two operands of several singletons each: where they are equal, each is one
// the other may be.
function bothUnions(x: "a" | "b", y: "b" | "c"): "b" | null {
  if (x === y) {
    const b: "b" = x;
    const c: "b" = y;
    return c;
  }
  return null;
}

type Tagged = { tag: 0 | 1; a: string } | { tag: 2; b: number };

function fieldAgainstUnion(o: Tagged, x: 0 | 1): string {
  if (o.tag === x) {
    return o.a;
  }
  return "";
}

// A test whose outcome the operand's type rules out is never taken.
function onlyTrue(x: true): number {
  if (x) {
    return 1;
  } else {
    const n: never = x;
    return n;
  }
}

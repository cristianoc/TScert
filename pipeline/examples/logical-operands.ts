// `&&` and `||` return an operand; a value that is not a Boolean is a
// condition by its truthiness (JavaScript's ToBoolean).
function andUndef(o: { a: number } | undefined, n: number): undefined | number {
  return o && n;
}

function orObj(
  o: { a: number } | undefined,
  d: { b: number },
): { a: number } | { b: number } {
  return o || d;
}

// The right operand sees the left one truthy.
function andNarrows(o: { a: number } | undefined): undefined | number {
  return o && o.a;
}

function boolAnd(x: boolean, y: boolean): boolean {
  return x && y;
}

function checkedSelection(x: { f: number } | undefined): number {
  const y = x || { f: 0 };
  return y.f;
}

function truthyGuard(o: { a: number } | undefined): number {
  if (o) {
    return o.a;
  }
  return 0;
}

function notObject(o: { a: number } | undefined): boolean {
  return !o;
}

// Singletons settle their truthiness: `0`, `""` and `0n` are falsy.
function zeroAnd(x: 0 | 1, s: string): 0 | string {
  return x && s;
}

function emptyOr(s: "" | "a"): "a" | "b" {
  return s || "b";
}

function bigintAnd(b: 0n | 1n, s: string): 0n | string {
  return b && s;
}

// A number or a string is either, and both arms are taken.
function stringOr(s: string, d: "x"): string {
  return s || d;
}

function numberAnd(n: number, s: string): number | string {
  return n && s;
}

function notNumber(n: number): boolean {
  if (!n) {
    return true;
  }
  return false;
}

function inClosure(o: { a: number } | undefined): number | undefined {
  const f = (p: { a: number } | undefined): number | undefined => p && p.a;
  return f(o);
}

// A false `&&` came from either operand: `x` is 1 or 2 there.
function disjunctiveOutcome(x: 1 | 2 | 3): 1 | 2 {
  if (x !== 1 && x !== 2) {
    return 1;
  } else {
    return x;
  }
}

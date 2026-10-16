// A guard's promise is part of its function type, checked at its body and
// narrowing its argument where a call answers `true`: over a union of
// literals, of primitive kinds and of `null`, in a statement, a ternary, a
// conjunction and a negated early return; a module constant's arrow guard; a
// guard closure; a guard catching its own exception; an assertion function;
// a guard passed as a plain predicate.
export type Presence = "dense" | "readable" | "sparse";

export function isPresence(value: unknown): value is Presence {
  return value === "dense" || value === "readable" || value === "sparse";
}

export function isText(x: string | number | null): x is string | null {
  if (typeof x === "string") return true;
  return x === null;
}

const isNumber = (v: unknown): v is number => typeof v === "number";

export function str(v: unknown): asserts v is string {
  if (typeof v !== "string") throw Error("expected a string");
}

function prefix(p: Presence): string {
  return p;
}

export function describe(v: unknown): string {
  if (isPresence(v)) return prefix(v);
  return isNumber(v) ? (v * 2).toString() : "none";
}

export function first(v: unknown): string {
  if (!isPresence(v)) return "none";
  return prefix(v);
}

export function small(a: unknown): boolean {
  return isNumber(a) && a < 1;
}

export function textLength(x: string | number | null): number {
  if (isText(x)) return x === null ? 0 : x.length;
  return -1;
}

export function length(v: unknown): number {
  str(v);
  return v.length;
}

export function predicate(): (v: unknown) => boolean {
  return isNumber;
}

export function size(v: unknown): number {
  const isString = (x: unknown): x is string => typeof x === "string";
  return isString(v) ? v.length : 0;
}

export function isWord(x: unknown): x is string {
  try {
    if (typeof x === "string") return true;
    throw Error("not a string");
  } catch {
    return false;
  }
}

export function wordLength(v: unknown): number {
  return isWord(v) ? v.length : 0;
}

// A named closure whose parameter is wider than the element of the array it
// is passed to, here a union of which the element is one arm: it is offered
// the callback's longer signature at the element, and Lean checks its body
// there, the element within the closure's parameter.
type F = { k: "f"; n: number };
type A = { k: "a"; s: string };
type T = A | F;

export function visit(t: T): number {
  return t.k === "f" ? t.n : t.s.length;
}

export function each(calls: F[]): number {
  let total = 0;
  const go = (part: T): void => {
    total += visit(part);
  };
  calls.forEach(go);
  return total;
}

export function mapped(calls: F[]): string[] {
  const name = (t: T): string => t.k;
  return calls.map(name);
}

export function tested(calls: readonly F[]): boolean {
  const small = (t: T): boolean => visit(t) < 10;
  return calls.every(small) && calls.some(small);
}

// The element written inline, the parameter a written union of aliases.
export function inline(calls: { k: "f"; n: number }[]): number {
  let total = 0;
  const go = (part: A | F): void => {
    total += visit(part);
  };
  calls.forEach(go);
  return total;
}

// The element an alias of the union's arm, the parameter wider still.
type G = F;
export function widest(calls: G[]): string[] {
  const show = (v: T | null): string => (v === null ? "" : v.k);
  return calls.map(show);
}

// The closure changing storage: a captured array it pushes onto, and the
// mapped array itself, whose result is read with its holes.
export function collected(calls: F[]): string[] {
  const out: string[] = [];
  const add = (t: T): void => {
    out.push(t.k);
  };
  calls.forEach(add);
  return out;
}

export function shrinking(calls: F[]): (string | undefined)[] {
  const name = (t: T): string => {
    calls.pop();
    return t.k;
  };
  return calls.map(name);
}

// A guard closure wider than the element: `filter`'s guard overload.
export function present(calls: (F | null)[]): F[] {
  const isF = (t: T | null): t is F => t !== null && t.k === "f";
  return calls.filter(isF);
}

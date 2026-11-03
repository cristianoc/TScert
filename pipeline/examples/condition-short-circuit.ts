// Conditions read by the short-circuit translation: each operand is
// dispatched on its truth where the operands before it left the outcome
// open, `!` exchanging the outcomes, so each operand's narrowing reaches the
// edge where it holds and no edge reaches a statement on a path no run takes.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
function isRecord(v: Json | undefined): v is Fields {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
// A test, then an operand that is no test.
export function testThenValue(p: string | undefined, n: number): string {
  if (p === undefined || n) return "";
  return p;
}
// A negated operand that is no test.
export function negatedValue(s: string | undefined, n: number): number {
  if (!s || n > 3) return 0;
  return s.length;
}
// A negated guard, then two operands that are no tests.
export function negatedGuardValues(
  v: Json | undefined,
  n: number,
  m: string,
): Fields {
  if (!isRecord(v) || n || m) throw Error("invalid");
  return v;
}
// A guard under `!` as the right operand.
export function guardRight(v: Json | undefined, n: number): Fields {
  if (n > 3 || !isRecord(v)) throw Error("invalid");
  return v;
}
// Nested negations.
export function nested(p: string | undefined, q: string | undefined): number {
  if (!(!(p !== undefined) || !(q !== undefined))) return p.length + q.length;
  return 0;
}
// `&&` over `||`.
export function mixed(
  p: string | undefined,
  q: string | undefined,
  n: number,
): number {
  if (p !== undefined && (q !== undefined || n > 0)) return p.length;
  return 0;
}
// `?:` as a condition, its arms tests.
export function chosen(p: string | undefined, n: number): number {
  if (p !== undefined ? p.length > 2 : n > 0) return 1;
  return 0;
}
// An optional chain's length, negated.
export function optionalLength(
  o: { readonly p?: readonly string[] },
  n: number,
): number {
  if (!o.p?.length || n > 3) return 0;
  return o.p.length;
}
// A discriminant's tests, one negated.
type K = { kind: "a"; a: string } | { kind: "b"; b: number } | { kind: "c" };
export function kinds(k: K): number {
  if (k.kind === "c" || !(k.kind === "a")) return 0;
  return k.a.length;
}
// A known Boolean tested again: where `c && x` failed with `c` true, `!c`
// answers `false`, and no edge carries `c` true where `!c` held.
export function known(c: boolean, p: string | undefined, x: boolean): number {
  if ((c && x) || (!c && p === undefined)) return 0;
  return c ? 1 : p === undefined ? 2 : p.length;
}
export function retested(c: boolean, d: boolean): number {
  if ((c && d) || !c) return 0;
  const t: true = c;
  return t ? 1 : 2;
}
// A negated test, then operands that are no tests: where `m.n` is truthy
// the condition holds, so past it `m.q` is falsy.
type M = { kind: "method"; n?: number; q?: true } | { kind: "field" };
export function retestedOperand(m: M): number {
  if (!(m.kind === "method") || m.n || m.q) return 0;
  const q: undefined = m.q;
  return q === undefined ? 1 : 2;
}
// Operands evaluated once each, in order: calls that write and may throw,
// and a comma's effect.
function step(log: string[], name: string): boolean {
  if (name === "") throw Error("unnamed");
  log.push(name);
  return name.length > 1;
}
export function ordered(log: string[], first: string | undefined): string[] {
  if (
    (first !== undefined && step(log, first)) ||
    (log.push("c"), !step(log, "d"))
  )
    log.push("e");
  return log;
}
// A loop's condition, tested again after `continue`.
export function drain(next: () => string | undefined): number {
  let total = 0;
  let item = next();
  while (item !== undefined && !(item.length > 3 || total > 10)) {
    total += item.length;
    item = next();
    if (total < 2) continue;
  }
  return total;
}
// A value-position operator yields its selected operand.
export function selected(
  p: string | undefined,
  n: number,
): string | number | undefined {
  const v = p && n;
  if (v) return v;
  return p;
}

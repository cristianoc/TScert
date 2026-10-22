// An object literal a closure without a result annotation returns, and a
// constant's literal a later spread copies, own exactly the keys they write:
// the copy keeps every key written before it that the spread's literals
// lack (SOURCE-MODEL.md, "Object literals").
type P = { name: string; type: number; dots: boolean };

// A closure's literals, spread, then mapped at TypeScript's inferred union
// `{ name, type, rest: true } | { name, type, rest?: undefined }`.
export function params(ps: P[]): [string, number][] {
  const rest = (p: P) => (p.dots ? { rest: true as const } : {});
  const all = ps.map((p, i) => {
    if (p.dots) return { name: p.name, type: p.type, ...rest(p) };
    return { name: "x" + i, type: 0 };
  });
  return all.map((q): [string, number] => [q.name, q.type]);
}

// A constant's literals, spread.
export function local(p: P): string {
  const extra = p.dots ? { rest: true as const } : {};
  const o = { name: p.name, ...extra };
  return o.name;
}

// A key two spreads may give: the later one's where it holds it.
export function twice(p: P): number | string {
  const a = () => ({ k: 1 });
  const b = () => (p.dots ? { k: "s" } : {});
  const o = { ...a(), ...b() };
  return o.k;
}

// A key a spread may give, then written: the written one's.
export function later(p: P): string {
  const o = { ...(p.dots ? { name: 1 } : {}), name: "x" };
  return o.name;
}

// An async closure's literals: the payload its promise resolves with.
export async function awaited(p: P): Promise<string> {
  const rest = async () => (p.dots ? { rest: true as const } : {});
  const o = { name: p.name, ...(await rest()) };
  return o.name;
}

// A literal a writable dictionary is expected at is allocated at it: no
// own-key bound meets a writable index.
export function dictionary(): Record<string, number> {
  const make: () => Record<string, number> = () => ({ a: 1 });
  return make();
}

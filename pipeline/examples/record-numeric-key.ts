// `Record<number, V>`, and a mapped type over `number`, is a number index:
// it constrains the canonical numeric keys; over `symbol`, a symbol index.
type NumberMap<V> = { [P in number]: V };
function same(r: Record<number, string>): Record<number, string> {
  return r;
}
function make(): NumberMap<string> {
  return { 0: "a", 1: "b" };
}
function symbols(): Record<symbol, boolean> {
  return {};
}
function every(): Record<string | number | symbol, number> {
  return {};
}
export function use(): string | undefined {
  const s: Record<symbol, boolean> = symbols();
  const e: Record<string | number | symbol, number> = every();
  return same(make())[1];
}

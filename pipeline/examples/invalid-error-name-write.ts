// TypeScript reads an error at `{ name: string | number }`, through which a
// number may be written over the `name` it reads at `string` (run under Node:
// `main()` returns 5). An error meets no record owning `name`.
export function main(): string {
  const e = new Error("m");
  const r: { name: string | number } = e;
  r.name = 5;
  return e.name;
}

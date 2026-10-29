// A local alias naming the result of a module function through
// ReturnType of its typeof, and NonNullable of that.
// Census functions:
// declaration-graph.mts#collectDeclarations.
interface Found {
  name: string;
}
function find(names: string[]): Found | null {
  const [first] = names;
  return first === undefined ? null : { name: first };
}
export function nameOf(names: string[]): string {
  type Target = NonNullable<ReturnType<typeof find>>;
  const found: Target | null = find(names);
  return found ? found.name : "";
}

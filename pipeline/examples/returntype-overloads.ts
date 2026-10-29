// ReturnType of a function's typeof is its declared result: of the last
// signature of an overload set, as TypeScript infers, and of each member of
// a union of typeofs. The overload set is the environment's, declared.
interface Found {
  name: string;
}
declare function pick(n: number): string;
declare function pick(s: string): Found;
function count(names: string[]): number {
  return names.length;
}
export function described(names: string[]): string {
  type Picked = ReturnType<typeof pick>;
  type Either = ReturnType<typeof count | typeof pick>;
  const picked: Picked = pick("a");
  const either: Either = count(names);
  return typeof either === "number" ? picked.name : either.name;
}

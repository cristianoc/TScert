// `console.log` formats every reachable key of an object argument: it takes
// primitives only (COMPILER-API.md, "Operations and their obligations").
export function log(o: { a: number }): void {
  console.log(o);
}

// A function's own `name` is not writable: `Object.assign` throws writing it,
// so a literal naming it is no callable object's fields.
export function named(): (n: number) => number {
  return Object.assign((n: number) => n, { name: "id" });
}

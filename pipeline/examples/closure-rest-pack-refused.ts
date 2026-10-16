// A closure's rest typed by its own type parameter: the closure's scheme
// reads a bound as the meet of its binder with it, and argument lists have no
// meet row, so no store contract fits the array its call collects.
export function count(): number {
  const bare = <T extends readonly number[]>(...args: T): number => args.length;
  return bare(1, 2);
}

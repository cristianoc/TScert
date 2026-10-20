// An instantiated callable type literal carries both its signature and its
// property contract. The contextual signature reading refuses that combination.
interface Box<T> {
  use(cb: { (x: T): number; label: string }): number;
}

export function run(): Box<string> {
  return {
    use(cb) {
      return cb("text") + cb.label.length;
    },
  };
}

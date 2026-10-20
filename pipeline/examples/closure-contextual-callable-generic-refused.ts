// A closure parameter TypeScript types from its context as a generic
// declaration's generic function type at an instance: read through its
// signature, whose type parameters the instance's reading does not state, so
// the parameter is refused; an annotation states it.
interface Box<T> {
  use(cb: (f: <U>(x: U) => T) => number): number;
}

function constant<U>(x: U): string {
  return typeof x;
}

function useBox(box: Box<string>): number {
  return box.use((f) => f(1).length);
}

export function run(): number {
  return useBox({
    use(cb) {
      return cb(constant);
    },
  });
}

// A generic method one of whose parameters holds another generic method: the
// nested generic method is outside the fragment, so the declaration is
// refused. Read as `unknown`, `run` would admit any value, such as 42.
interface Runner {
  run<P extends unknown[]>(helper: { id<P>(x: P): P }, ...args: P): number;
}

export function wrong(): Runner {
  // @ts-expect-error
  return { run: 42 };
}

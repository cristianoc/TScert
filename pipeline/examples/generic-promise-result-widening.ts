type Exact = <T>(value: T, result: Awaited<T>) => Promise<Awaited<T>>;
type Widened = <T>(value: T, result: Awaited<T>) => Promise<unknown>;

export function widen(wrapper: Exact): Widened {
  return wrapper;
}

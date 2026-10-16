type Exact = <T>(value: T) => Promise<Awaited<T>>;
type Erased = <T>(value: T) => Promise<unknown>;

export function erase(wrapper: Exact): Erased {
  return wrapper;
}

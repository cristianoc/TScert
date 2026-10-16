type NumericWrapper = <T extends number>(value: T | Promise<T>) => Promise<T>;
type UnknownWrapper = <T>(value: T | Promise<T>) => Promise<unknown>;

export function eraseInputBound(wrapper: NumericWrapper): UnknownWrapper {
  return wrapper;
}

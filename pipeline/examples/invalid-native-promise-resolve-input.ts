export function openResolve<T>(value: T): Promise<unknown> {
  return Promise.resolve(value);
}

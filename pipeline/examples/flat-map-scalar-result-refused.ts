// A `flatMap` callback returning a string or an empty array: a string is
// never an array, so `flatMap` appends it as it is, but the overlay states
// only callbacks returning arrays.
export function present(
  keys: string[],
  get: (key: string) => string | undefined,
): string[] {
  return keys.flatMap((key: string) => {
    const value = get(key);
    if (value === undefined) return [];
    return `${key}=${value}`;
  });
}

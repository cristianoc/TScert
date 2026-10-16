// A call through a union of functions carrying different fields and results:
// every arm accepts the argument, so the call's result is their results'
// union. The producer states no claim for a call on such a union.
type Callable = ((x: boolean) => boolean) & { value: boolean };
type Nothing = ((x: boolean) => null) & { value: null };

export function call(f: Callable | Nothing): boolean | null {
  return f(true);
}

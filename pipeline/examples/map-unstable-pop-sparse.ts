// Program 7 at a result type admitting holes: the callback pops the array
// `map` is reading, so `map` takes its unrestricted signature and the result
// may hold holes, which `(number | undefined)[]` admits.
export function shrink(xs: number[]): (number | undefined)[] {
  return xs.map((x: number): number => {
    xs.pop();
    return x;
  });
}

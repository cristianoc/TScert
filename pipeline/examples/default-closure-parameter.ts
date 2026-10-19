// A parameter whose default is a closure holds the function type it states,
// whichever value it took: the closure, taking fewer parameters, is built at
// that type, and a call passes the parameter's actuals.
export function runs(
  n: number,
  except: (n: number) => boolean = () => false,
): boolean {
  return except(n);
}
export function counted(
  xs: number[],
  keep: (x: number, i: number) => boolean = (x) => x > 0,
): number {
  return xs.filter((x, i) => keep(x, i)).length;
}

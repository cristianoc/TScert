// Copying a constructor onto an array would change native result construction.
export function replace(replacement: Function): number[] {
  const xs: number[] = [1, 2];
  Object.assign(xs, { constructor: replacement });
  return xs;
}

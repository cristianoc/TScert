// A declaration's `any` is read as `unknown`: its field accepts any value.
interface Loose {
  x: any;
}
export function store(l: Loose, n: number): number {
  l.x = n;
  return n;
}

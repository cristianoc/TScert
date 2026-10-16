// A declaration's `any` is read as `unknown`, never as every type: its field
// is not a number.
interface Loose {
  x: any;
}
export function wrong(l: Loose): number {
  return l.x;
}

// An optional field without an initializer holds `undefined` from the
// instance's creation: the class declares it as TypeScript does,
// `label?: string | undefined`, which that `undefined` meets.
export class Tagged {
  count: number = 0;
  label?: string;
}
export function labelOf(t: Tagged): string | undefined {
  return t.label;
}

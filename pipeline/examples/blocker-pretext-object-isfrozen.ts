// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#findSegmentSources.
// Refusal: gate: Object.isFrozen is not in the reviewed overlay of library
// globals: isFrozen(o: any): boolean;.
// `Object.isFrozen`, not in the reviewed overlay of library globals.
export function frozen(o: { items: string[] }): boolean {
  return Object.isFrozen(o);
}

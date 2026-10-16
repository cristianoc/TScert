// A record type bounds no key but its own: `{ readonly a: number }` may own
// others, of any value, so the generic `Object.values`, which TypeScript
// selects for it at `number`, is read at a dictionary it is not.
function values(d: { readonly a: number }): number[] {
  return Object.values(d);
}

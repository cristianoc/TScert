// TypeScript gives an object type with no numeric member an implicit number
// index, though the object may own numeric keys of any type: a record's type
// says nothing of the keys it does not name.
function implicit(x: { readonly a: number }): { readonly [k: number]: string } {
  return x;
}

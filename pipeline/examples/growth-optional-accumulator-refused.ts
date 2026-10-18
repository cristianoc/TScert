// A key-adding write merges onto the local's object, typed by its annotation:
// a record of optional fields alone may be a host object, on which a merge is
// stuck (COMPILER-API.md, "Restricted values"). The object is the literal's,
// which the annotation does not say.
export function optionalAnnotated(): { a?: number } {
  const o: { a?: number } = {};
  o.a = 3;
  return o;
}

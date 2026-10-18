// A value stored in a container keeps its type: a spread of a record of
// readonly fields alone read back from a field is refused (R8,
// COMPILER-API.md).
export function launder(o: { readonly a: number }): {} {
  const box = { inner: o };
  return { ...box.inner };
}

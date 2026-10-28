// `flat()` flattens each element that is an array, whatever its declared
// type: at `object[]` holding `[1]`, TypeScript's `FlatArray` gives `object[]`
// and the native gives `[1]`. `flat` is stated at a receiver of arrays only,
// so this call is refused. Under Node `typeof flatObjects([[1]])[0]` is
// "number".
export function flatObjects(values: object[]): object[] {
  return values.flat();
}

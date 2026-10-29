// A closure at a generic signature instantiated at a type parameter of the
// enclosing function spelled as the signature's own: its parameters'
// contextual types name both, the outer R and the closure's R, with one
// spelling, so they are refused.
type Reader<X> = <R>(body: X, read: (text: X) => R) => R;
export function kept<R>(value: R): R {
  const reader: Reader<R> = (body, read) => read(body);
  return reader(value, v => v);
}

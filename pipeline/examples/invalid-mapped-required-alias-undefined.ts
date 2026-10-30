// Without `exactOptionalPropertyTypes`, `Required<{ b?: string | Again }>`,
// `Again` an alias of an alias of `undefined`, is `{ b: string }`: a record
// holding `undefined` at `b` does not meet it.
type Missing = undefined;
type Again = Missing;
export function make(): Required<{ b?: string | Again }> {
  const b: string | Again = undefined;
  return { b };
}

// `Required` over an optional field whose type names an alias of `undefined`:
// the reader refuses the field as it does a written `undefined`.
type Missing = undefined;
export function make(): Required<{ b?: string | Missing }> {
  return { b: "b" };
}

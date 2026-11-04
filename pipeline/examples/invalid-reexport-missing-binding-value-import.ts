// A re-export of a binding its module does not export: TypeScript refuses it,
// and so does the gate, as it refuses an import of the binding.
export { missing } from "@fixture/lib";

export function quadruple(x: number): number {
  return x * 4;
}

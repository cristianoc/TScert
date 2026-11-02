// Census functions:
// declaration-graph.mts#closeDeclarations
// declaration-graph.mts#collectFrom
// declaration-graph.mts#collectInstances
// declaration-graph.mts#collect
// declaration-graph.mts#elaborateDeclaration
type Signature = { kind: "call"; params: number[] } | { kind: "construct" };
export function transform(fields: { signatures: Signature[] }[]): number[] {
  const nativeFields = fields.map((field): number => {
    const signatures = field.signatures.filter(
      (s): s is Extract<Signature, { kind: "call" }> => s.kind === "call",
    );
    return signatures.length;
  });
  return nativeFields.map((field) => field);
}

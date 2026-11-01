// Typed decoder results retain the fields checked while building fresh storage.
// Census functions:
// source-flow.mts#decodeFlowDocument
function record(value: { readonly id: unknown }): { id: string } {
  const id = value.id;
  if (typeof id !== "string") throw Error("string required");
  return { id };
}

export function decode(value: { readonly id: unknown }[]): { id: string }[] {
  const document = value.map(record);
  return document;
}

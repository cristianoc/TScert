// A typed intermediate widened to unknown before its closing assertion.
// Census functions:
// source-flow.mts#decodeFlowDocument
export function decode(value: { id: string }): { id: string } {
  const document: unknown = value;
  return document as { id: string };
}

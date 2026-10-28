// Array.isArray of a value typed unknown finds an array other code may hold
// at its own element type: the test gives a read-only view, which the code
// returns as a writable array.
// Census functions:
// source-flow.mts#decodeFlowDocument.
function invalid(message: string): never {
  throw Error(message);
}
export const array = (value: unknown): unknown[] =>
  Array.isArray(value) ? value : invalid("array required");

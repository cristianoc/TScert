// An arrow guard promising `number[]` answers `true` of any array: a string
// array passes, which the promise does not admit.
export const isNumbers = (v: number[] | string[]): v is number[] =>
  Array.isArray(v);

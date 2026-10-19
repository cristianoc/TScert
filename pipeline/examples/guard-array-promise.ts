// A guard promising an array, as a function and as an arrow: the promise is
// lowered with the array's labels, and both forms check it alike.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function isListed(v: Json): v is Json[] {
  return Array.isArray(v);
}
export const isList = (v: Json): v is Json[] => Array.isArray(v);
export const isNumbers = (v: number[] | string): v is number[] =>
  Array.isArray(v);
export function count(v: Json): number {
  return isList(v) ? v.length : isListed(v) ? -1 : 0;
}

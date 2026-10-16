// TypeScript lets a mutable object with a number index pass as a mutable
// string index alone, through which a numeric key may be given a string that a
// holder of the number index reads as a number.
interface Dual {
  [k: string]: number | string;
  [k: number]: number;
}
function forget(d: Dual): { [k: string]: number | string } {
  return d;
}

// Every numeric key is a string key: an index over `string | number`, and a
// number index beside a string index of the same contract, are the string
// index alone.
type Either = { [k: string | number]: number };
interface Dual {
  readonly [k: string]: string;
  readonly [k: number]: string;
}
function either(x: Either): number | undefined {
  return x["k"];
}
function dual(x: Dual): string | undefined {
  return x["k"];
}
export function use(e: Either, d: Dual): number {
  return (either(e) ?? 0) + (dual(d) ?? "").length;
}

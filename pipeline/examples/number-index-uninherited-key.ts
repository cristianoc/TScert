// A number index signature constrains the canonical numeric keys ("0",
// "1.5", "-1", "NaN"), the keys `o[n]` reaches for a number `n`, apart from
// the other string keys; a string index beside it constrains every string key.
interface Dual {
  readonly [k: string]: number | string;
  readonly [k: number]: number;
}
type Numbers = { readonly [k: number]: string };
type Named = { readonly name: string; readonly [k: number]: boolean };
interface Strings {
  [k: string]: number;
}
interface Counts {
  [k: number]: number;
}

// A numeric key, by a number or its spelling, reads through the number index.
function first(x: Numbers): string | undefined {
  return x[0];
}
function spelled(x: Numbers): string | undefined {
  const a = x["1.5"];
  const b = x["-1"];
  return x["NaN"] ?? a ?? b;
}
function dynamic(x: Numbers, n: number): string | undefined {
  return x[n];
}
// Every other string key reads through the string index.
function dualString(x: Dual, k: "key" | "a"): number | string | undefined {
  return x["key"] ?? x[k];
}
function dualNumber(x: Dual, n: number): number | undefined {
  return x[0] ?? x[n];
}
// A named member beside a number index reads at its own contract.
function named(x: Named): string {
  return x.name;
}
// A number reads a string index too: its key is a string.
function throughStrings(x: Strings, n: number): number | undefined {
  return x[n];
}
// A string index constrains the numeric keys too, so it is a number index at
// its contract, writable as it is.
function narrow(x: Strings): Counts {
  return x;
}
function forget(x: Dual): Numbers | { readonly [k: number]: number } {
  return x;
}
// A fresh literal meets a number index through its own keys: `name` is no
// number's spelling, so only `0` and `1` are held to it.
function make(): Named {
  return { name: "n", 0: true, 1: false };
}
export function use(n: number): number {
  const x: Numbers = { 0: "a", 1.5: "b" };
  const d: Dual = { 0: 1, a: "a" };
  const s: Strings = { a: 1 };
  const counts: Counts = narrow(s);
  return (
    (first(x) ?? "").length +
    (spelled(x) ?? "").length +
    (dynamic(x, n) ?? "").length +
    (dualString(d, "a") === 1 ? 1 : 0) +
    (dualNumber(d, n) ?? 0) +
    named(make()).length +
    (throughStrings(s, n) ?? 0) +
    (counts[0] ?? 0) +
    (forget(d)[0] === 1 ? 1 : 0)
  );
}

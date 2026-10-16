// A primitive's members: a string's own `length` and code units, and every
// other member read through its wrapper's prototype, with the primitive as
// receiver.
function stringLength(s: string): number {
  return s.length;
}

function literalLength(x: "ab" | "c"): number {
  return x.length;
}

function upper(s: string): string {
  return s.toUpperCase();
}

function chained(s: string): number {
  return s.trim().indexOf("a");
}

function hex(n: number): string {
  return n.toString(16);
}

function fixed(n: number): string {
  return n.toFixed(2);
}

function bigintString(b: bigint): string {
  return b.toString();
}

function booleanString(b: boolean): string {
  return b.toString();
}

function locales(n: number, b: bigint): string {
  const m: string = n.toLocaleString();
  return b.toLocaleString();
}

function literalReceivers(): string {
  const s = "hello";
  const u: string = s.toUpperCase();
  const n = 255;
  return n.toString(16);
}

// Any numeric index reads a code unit or `undefined`.
function codeUnit(s: string, i: number): string | undefined {
  return s[i];
}

function pastTheEnd(s: string): string | undefined {
  return s[10];
}

function namedLength(s: string): number {
  return s["length"];
}

function inClosures(s: string): number {
  const f = (t: string): number => t.length + t.indexOf("a");
  const g = (t: string): string | undefined => t[0];
  const h = (t: string): string => t.toUpperCase().trim();
  return f(h(s)) + (g(s) === undefined ? 0 : 1);
}

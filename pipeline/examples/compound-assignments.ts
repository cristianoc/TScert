// Increments and compound assignments read the target once, at its storage
// contract, and write the operation's value back; `??=`, `||=` and `&&=`
// write only on the arm the test selects.
function count(limit: number): number {
  let k: number = 0;
  let steps: number = 0;
  while (k < limit) {
    k++;
    steps += 2;
  }
  const old: number = k--;
  --k;
  k *= 3;
  k **= 2;
  k /= 4;
  k -= old;
  return ++steps + k;
}
function bump(o: { n: number }, key: { m: bigint }): number {
  o.n++;
  o["n"] += 10;
  key.m++;
  key["m"] *= 2n;
  return o.n--;
}
function fill(o: { n: number | undefined; flag: boolean }): number {
  o.n ??= 7;
  o.flag ||= o.n === undefined;
  o.flag &&= false;
  const n: number | undefined = o.n;
  return n === undefined ? 0 : n;
}
function fallback(x: string | undefined): string {
  let y: string | undefined = x;
  y ??= "none";
  return y;
}
function toggled(b: boolean): boolean {
  let on: boolean = b;
  on ||= false;
  on &&= b;
  return on;
}
function suffix(s: string, n: number): string {
  let out: string = s;
  out += n;
  out += "!";
  return out;
}

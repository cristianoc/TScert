// `+` with a string operand concatenates; the other operand, a primitive
// other than a symbol, converts by ToString. A template literal is the
// concatenation of its parts.
function greet(name: string): string {
  return "Hello, " + name;
}
function label(n: number, b: boolean, i: bigint): string {
  return n + ": " + b + " " + i;
}
function absent(u: undefined, z: null): string {
  return "u=" + u + ", z=" + z;
}
function row(name: string, count: number, done: boolean): string {
  return `${name} (${count}) ${done ? "done" : "open"}`;
}
function sized(i: bigint, u: undefined, z: null): string {
  return `i=${i} u=${u} z=${z}`;
}
function fixed(): string {
  return `plain`;
}
function nested(n: number): string {
  return `[${`<${n}>`}] ${"(" + n + ")"}`;
}
function joined(parts: string[]): string {
  let out: string = "";
  for (const p of parts) {
    out += p;
    out += ",";
  }
  return out + parts.length;
}
function before(a: string, b: string): boolean {
  return a + "!" < b;
}

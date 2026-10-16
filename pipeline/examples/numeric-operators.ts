// Relational comparisons, `**`, `%` and the unary numeric operators on numbers.
function less(a: number, b: number): boolean {
  return a < b;
}
function atMost(a: number, b: number): boolean {
  return a <= b;
}
function clamp(value: number, limit: number): number {
  if (value > limit) {
    return limit;
  }
  return value;
}
function square(x: number): number {
  return x ** 2;
}
function negate(x: number): number {
  return -x;
}
function toNumber(x: number): number {
  return +x;
}
function complement(x: number): number {
  return ~x;
}
function before(a: string, b: string): boolean {
  return a >= b;
}
function sumBelow(limit: number): number {
  let total: number = 0;
  let i: number = 0;
  while (i < limit) {
    total = total + i;
    i = i + 1;
  }
  return total;
}
// An array's length is a number, compared and computed with like any other.
function count(values: number[]): number {
  let i: number = 0;
  while (i < values.length) {
    i = i + 1;
  }
  return i;
}
function lastIndex(values: readonly string[]): number {
  return values.length - 1;
}
function isEven(n: number): boolean {
  return n % 2 === 0;
}
function wrap(i: number, size: number): number {
  let k: number = i;
  k %= size;
  return k;
}
function bothSet(n: number, m: number): boolean {
  return n === 25 && m !== 3;
}

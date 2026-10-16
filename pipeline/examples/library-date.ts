// `Date` through the reviewed overlay: `new Date()`, `new Date(v)` of a
// number or a string, `new Date(y, m, ...)` of numbers, each a `Date`, and
// its getters, numbers. An invalid date is a `Date` whose getters give `NaN`.
function test(): number {
  const d1: Date = new Date("2024-01-01T00:00:00Z");
  const d3: number = new Date("2024-01-01T00:00:00Z").getTime();
  const d4: Date = new Date(2024, 0, 1);
  const d5: Date = new Date();
  return d3 + d4.getFullYear() + d5.getMonth() + d1.valueOf();
}

function iso(ms: number): string {
  return new Date(ms).toISOString();
}

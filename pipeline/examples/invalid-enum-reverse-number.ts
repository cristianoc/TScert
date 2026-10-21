// A numeric enum's object holds a reverse key at its members' values: at an
// arbitrary number the read may be undefined, which TypeScript types as
// `string`.
enum Level {
  Low = 1,
  High = 2,
}
function levelName(n: number): number {
  return Level[n].length;
}

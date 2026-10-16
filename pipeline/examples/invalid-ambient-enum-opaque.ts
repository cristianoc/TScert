// An uninitialized member of an ambient enum is opaque, as TypeScript reads
// it: the declaration does not state its value, whatever auto-increment
// suggests, so it is a number, not 1.
declare enum Level {
  Low = 0,
  High,
}
export function high(): 1 {
  return Level.High;
}

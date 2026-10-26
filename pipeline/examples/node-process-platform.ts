// Node's `process.platform`, `process.arch` and `process.execArgv`, read
// through their overlay entries: two strings and a readonly array of strings.
export function target(): string {
  return `${process.platform}-${process.arch}`;
}
export function options(): string[] {
  return [...process.execArgv];
}

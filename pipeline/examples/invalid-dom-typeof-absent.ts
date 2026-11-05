// The branch where the host defines no `document`, as Node and a worker
// define none: `typeof document` answers "undefined" there, so the branch
// runs, and its read past the array's end answers `undefined`.
export function absent(names: string[]): string {
  if (typeof document === "undefined") return names[0];
  return "";
}

// Node's global `clearTimeout`, a function declared outside the standard
// library, read through its overlay entry: any value, no effect stated.
export function stop(id: number): void {
  clearTimeout(id);
}

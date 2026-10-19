// Node's global `queueMicrotask`, declared in an installed package, is a
// native function no reviewed entry lists: refused rather than read at its
// declaration.
export function later(): void {
  queueMicrotask(() => {});
}

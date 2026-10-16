// `declare let` is module storage that code outside the module may write at
// any time, a call included. The fragment has no module storage, so it is
// refused where it is declared.
declare let current: string | null;
export function read(): string | null {
  return current;
}

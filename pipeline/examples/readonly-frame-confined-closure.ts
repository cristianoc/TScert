// A row of records a frame allocates and fills through a closure it gives an internal
// helper: the closure is held by no storage and given to no outside code,
// so it runs only while the frame is active, which runs no outside code;
// no crossing can have reached the row when the closure pushes into it,
// and (O) admits the push, though released rows may come back read-only
// through `walk`.
function each(n: number, f: (i: number) => void): void {
  for (let i = 0; i < n; i++) f(i);
}

export function fill(n: number): { at: number }[] {
  const row: { at: number }[] = [];
  each(n, (i) => {
    row.push({ at: i });
  });
  return row;
}

export const walk = (h: unknown, visit: () => void): number => {
  visit();
  return h === undefined ? 0 : 1;
};

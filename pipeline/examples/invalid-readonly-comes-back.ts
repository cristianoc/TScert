// The module of readonly-frame-released-store with a walker taking
// `unknown`: the rows `rows` gives out may come back through it, read-only,
// so `fill`'s store into them installs a row the caller holds writable
// into storage the walker relies on (under Node, a visitor that fills a row
// and then truncates it makes `walk(rows(), …)` read `undefined`,
// tests/node-runs.mts). (O) refuses the store.
const held: number[][] = [];

export const rows = (): number[][] => held;

export const fill = (n: number): number[] => {
  const row: number[] = [];
  for (let i = 0; i < n; i++) row.push(1);
  held.push(row);
  return row;
};

export const walk = (h: unknown, visit: () => void): number => {
  const rs = h as readonly (readonly number[])[];
  visit();
  const row = rs[rs.length - 1];
  if (row === undefined) return 0;
  const n = row.length;
  let sum = 0;
  for (let i = 0; i < n; i++) {
    visit();
    sum += row[i] as number;
  }
  return sum;
};

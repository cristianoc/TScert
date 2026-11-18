// A module whose entries take only numbers: no released array of it can
// come back into it, so a store into one installs nothing a fact of the
// module relies on. `fill` stores a row it also gives out writable into the
// rows `rows` gives out writable, and the module's certificate holds.
const held: number[][] = [];

export const rows = (): number[][] => held;

export const fill = (n: number): number[] => {
  const row: number[] = [];
  for (let i = 0; i < n; i++) row.push(1);
  held.push(row);
  return row;
};

export const count = (n: number): number => held.length + n;

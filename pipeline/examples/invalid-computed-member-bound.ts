interface Cell<Flag extends boolean> {
  value: Flag extends true ? number : string;
}
export function use(cell: Cell<0>): void {}

type Cell<T> = { value: Awaited<T> };

export function widenAndWrite(cell: Cell<number>): void {
  const wider: Cell<number | string> = cell;
  wider.value = "changed";
}

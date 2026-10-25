export function write(g: { item: { value: number | string } }): void {
  const item = { value: 1 };
  g.item = item;
}

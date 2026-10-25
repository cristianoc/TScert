export function field(g: {
  items: (number | string)[];
  item: { value: number | string } | null;
}): void {
  g.items = [1];
  g.item = { value: 1 };
}
export function index(rows: number[][]): void {
  rows[0] = [];
}
export function dictionary(rows: { entry: { value: number | string } }): void {
  rows["entry"] = { value: 1 };
}
export class Bag {
  items: number[] = [];
  reset(): void {
    this.items = [];
  }
}

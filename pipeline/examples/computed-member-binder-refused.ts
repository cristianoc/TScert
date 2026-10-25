interface Cell<Flag extends boolean> {
  value: Flag extends true ? number : string;
}
export function use<Flag extends boolean>(cell: Cell<Flag>): void {}

interface Left {
  left: number;
}
interface Right {
  right: string;
}
declare function both(f: (x: Left & Right) => number): void;
export function wrong(): void {
  both((x) => x.right);
}

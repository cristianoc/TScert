// The same contracts reach the declaration graph from annotations and context.
interface Left {
  left: number;
}
interface Right {
  right: string;
}
interface Box<T> {
  value: T;
}
declare function both(f: (x: Left & Right) => number): void;
declare function arrays(f: (x: (Left & Right)[]) => number): void;
declare function boxes(f: (x: Box<Left & Right>) => string): void;
export function annotated(): void {
  both((x: Left & Right): number => x.left);
  arrays((xs: (Left & Right)[]): number => xs.length);
  boxes((x: Box<Left & Right>): string => x.value.right);
}
export function inferred(): void {
  both((x) => x.left);
  arrays((xs) => xs.length);
  boxes((x) => x.value.right);
}

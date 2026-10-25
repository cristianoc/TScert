class Box {
  value: number = 1;
}
export function use(apply: (callback: (ctor: typeof Box) => number) => number): number {
  return apply(ctor => 1);
}

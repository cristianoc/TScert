class Box {
  value: number = 1;
}
export function use(): number {
  const callable = Object.assign((ctor: typeof Box): number => 1, { tag: 1 });
  return callable(Box);
}

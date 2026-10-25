class Box {
  value: number = 1;
}
export function use(): number {
  const callable = Object.assign(() => Box, { tag: 1 });
  return callable().value;
}

class Box {
  constructor(public value: number) {}
}
export function incompatible(): number {
  const args: [string] = ["wrong"];
  // @ts-expect-error A string cannot fill the constructor's number parameter.
  return new Box(...args).value;
}

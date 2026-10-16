// A generic callback returning string cannot satisfy a boolean-result bound.
export function use(flag: boolean): boolean {
  const choose = <T extends (x: boolean) => boolean>(fn: T): T => fn;
  const wrong = <U>(value: U): string => "wrong";
  return choose(wrong)(flag);
}

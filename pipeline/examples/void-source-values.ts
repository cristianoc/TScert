export function returningVoid(): void {}

export function compareReturns(left: () => void, right: () => void): boolean {
  return left() === right();
}

export function compareArguments(left: void, right: void): boolean {
  return left !== right;
}

export function compareEmptyReturns(): boolean {
  return returningVoid() === returningVoid();
}

export function passHiddenNumber(): boolean {
  const value: () => void = () => 42;
  return compareArguments(value(), undefined);
}

export function passHiddenObject(): boolean {
  const value: () => void = () => ({ n: 42 });
  return compareReturns(value, value);
}

export function passHiddenArray(): boolean {
  const value: () => void = () => [42];
  return compareReturns(value, value);
}

export function passHiddenFunction(): boolean {
  const value: () => void = () => () => 42;
  return compareReturns(value, value);
}

export function passHiddenPrimitive(
  input: null | boolean | string | bigint | symbol,
): boolean {
  const value: () => void = () => input;
  return compareArguments(value(), undefined);
}

class Empty {}

export function passHiddenConstructor(): boolean {
  const value: () => void = () => Empty;
  return compareReturns(value, value);
}

export function keepPromise(input: Promise<void>): Promise<void> {
  return input;
}

export function defaultResult(value: () => void): void | number {
  return value() ?? 0;
}

export function defaultGeneric<T>(value: T | void): T | void | null {
  return value ?? null;
}

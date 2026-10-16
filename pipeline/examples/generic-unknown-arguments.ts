function identity<T>(value: T): T {
  return value;
}

export function forward(value: unknown): unknown {
  return identity(value);
}

export function caught(run: () => void): unknown {
  try {
    run();
    return undefined;
  } catch (error) {
    return identity(error);
  }
}

export function validVoidUnionUsage<T>(value: void | T): boolean {
  return value === value;
}

export function compareUnknown(left: unknown, right: unknown): boolean {
  return left === right;
}

export function compareGeneric<T>(left: T, right: T): boolean {
  return left !== right;
}

export function returned(run: () => unknown): unknown {
  return identity(run());
}

export function throwGeneric<T>(value: T): never {
  throw value;
}

export function rethrow(run: () => void): never {
  try {
    run();
    throw undefined;
  } catch (error) {
    throw identity(error);
  }
}

export function compareCaught(run: () => void): boolean {
  try {
    run();
    return true;
  } catch (error) {
    return error === identity(error);
  }
}

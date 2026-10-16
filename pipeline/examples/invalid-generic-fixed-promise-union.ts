function takePromiseOrString<T extends string>(x: Promise<number> | T): void {}

export function incompatible(p: Promise<string>): void {
  // @ts-expect-error Neither the fixed arm nor the bounded binder admits this promise.
  takePromiseOrString(p);
}

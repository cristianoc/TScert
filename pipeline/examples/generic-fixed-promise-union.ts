function takePromiseOrT<T>(x: Promise<number> | T): void {}

export function testPromiseInUnion(p: Promise<string>): void {
  takePromiseOrT(p);
}

export function fixedArm(p: Promise<number>): void {
  takePromiseOrT(p);
}

export function mixedArms(p: Promise<number> | Promise<string>): void {
  takePromiseOrT(p);
}

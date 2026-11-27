// An ambient class's method has no checked body: an external implementation or
// subclass may declare an optional second parameter reading `b.toUpperCase()`,
// so it does not gain a `...unknown[]` extension (TypeScript accepts this).
declare class AmbientOne {
  m(a: number): string;
}

interface TwoNum {
  m(a: number, b: number): string;
}

export function bad(x: AmbientOne): string {
  const t: TwoNum = x;
  return t.m(1, 42);
}

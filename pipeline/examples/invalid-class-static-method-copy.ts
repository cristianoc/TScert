// A class's static method is not enumerable: a copy of the class value takes
// its static fields and not the method.
class C {
  static readonly v: number = 1;
  static m(): number {
    return 1;
  }
}
export function copy(): { v: number; m: () => number } {
  return { ...C };
}

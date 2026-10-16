// A spread copies the own enumerable properties of its operand: a class
// value's are its static fields, which its type states; its static methods
// are none. A class value of a type stating no static field gives a copy
// stating none.
class StaticReader {
  static readonly value: number = 1;
  static readonly name0: string = "reader";
  static read(): number {
    return 1;
  }
}

export function copyStaticData(): number {
  const copy = { ...StaticReader };
  return copy.value + copy.name0.length;
}

export function spreadConstructor(c: new () => object): {} {
  return { ...c };
}

export function spreadOver(): { value: number; extra: boolean } {
  return { ...StaticReader, extra: true };
}

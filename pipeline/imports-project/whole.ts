// Declarations clients read as whole types (`*-whole-value-import` cases). No
// example imports this module's values, so nothing runs it.
type B<T extends string> = T;

// A class with an inferred member, consumed whole.
export class Inferred {
  m = "a" as keyof { a: B<any> };
}

// A namespace consumed whole: its members' annotations are swept.
export namespace Space {
  export const m: keyof { a: B<any> } = "a";
}

// A fully annotated class with a static block, which is code.
export class WithStatic {
  m: number = 1;
  static {
    console.log("hello");
  }
}

// An overload set, whose public signature states its type, and an accessor
// pair whose getter states the setter's type.
export function over(x: number): number;
export function over(x: number) {
  return x;
}
export class Paired {
  get m(): number {
    return 1;
  }
  set m(x) {}
}

// Constants whose literal initializers state their types.
export const { lm } = { lm: 1 };
// prettier-ignore
export const paren = (1);
export const plus = +1;

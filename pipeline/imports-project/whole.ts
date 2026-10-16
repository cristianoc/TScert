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

// Members the checker's symbols expose (`invalid-written-symbols-*` cases).
export declare namespace Ambient {
  const m: keyof { a: B<any> };
}
export namespace Dotted.inner {
  export const m: keyof { a: B<any> } = "a";
}
export const { dd = "a" as keyof { a: B<any> } } = {};
const key: keyof { a: B<any> } = "a";
export class ComputedName {
  [key]: number = 1;
}
export class Ctor {
  constructor(m: "a");
  constructor(public m: keyof { a: B<any> }) {}
}
export abstract class StaticMethod {
  abstract m(): number;
  static m() {
    return "a" as keyof { a: B<any> };
  }
}
export class StaticGetter {
  get m(): number {
    return 1;
  }
  static get m() {
    return "a" as keyof { a: B<any> };
  }
}
export const angled = { m: <number>1 };
export class Merged {}
export interface Merged {
  m: number;
}

// A constant of a mapped type, whose members the checker synthesises
// (`invalid-written-synthetic-member-value-import`), and a default export
// object with a computed key (`defaulted.ts` holds its own).
export declare const mappedConstant: {
  [K in "a"]: keyof { a: B<any> };
};
export declare const remapped: {
  [K in "x" as `${K}y`]: keyof { a: B<any> };
};
export class Bounded<T extends string> {}
export interface Bounded<T extends string> {}

// A class merged with an interface adding a member
// (`merged-class-consumer-value-import`): its instance contract is both.
export class Augmented {}
export interface Augmented {
  m: number;
}

// Members whose types come from instantiation, mapping or composition
// (`invalid-written-path-*` and `written-path-*` cases).
interface Box<T> {
  a: T;
}
export declare const boxed: Box<keyof { a: B<any> }>;
export declare const partial: Partial<Box<keyof { a: B<any> }>>;
export declare const picked: Pick<Box<keyof { a: B<any> }>, "a">;
export declare const readonlyBox: Readonly<Box<keyof { a: B<any> }>>;
export declare const required: Required<Box<keyof { a: B<any> }>>;
export declare const omitted: Omit<Box<keyof { a: B<any> }>, "b">;
export declare const unioned: Box<keyof { a: B<any> }> | { a: number };
export declare const intersected: Box<keyof { a: B<any> }> & { a: string };
declare const source: Box<keyof { a: B<any> }> & { b: number };
export const spread = { ...source };
export const { b: dropped, ...rest } = source;
type Homomorphic<T> = { [K in keyof T]: keyof { z: B<any> } };
export declare const homomorphic: Homomorphic<{ a: number }>;
export declare const nest: { [K in "a"]: { [J in "b"]: number } };
export declare const keyOwner: { [K in "a"]: "x" };
export interface ByPropertyKey {
  [keyOwner.a]: number;
}
export type Keys<T> = keyof T;
export declare const keyed: { [K in "a"]: number };

/* An external library declaring `any`, read by the controls through the
 * shadow program as every external declaration is. */
export interface Box<T> {
  value: T;
}
/** A result typed `any`: read as `unknown`. */
export declare const Factory: new () => Box<any>;
/** A property typed `any`: read as `unknown`. */
export declare const foreign: { x: any };
/** An index signature typed `any`: read as `unknown`. */
export declare const keyed: { [key: string]: any };
/** A callback's parameter typed `any`: the callback is given `unknown`. */
export declare const invoke: (f: (x: any) => void) => void;
/** The same through a rest parameter. */
export declare const invokeAll: (...fs: ((x: any) => void)[]) => void;
/** An input typed `any` no review states: refused at a use. */
export declare function consume(value: any): void;
/** A default `any` beside a constraint: the constraint holds. */
export declare function bounded<T extends number = any>(x: T): number;
type Anything = any;
/** An alias of `any` at an input. */
export declare function takesAlias(x: Anything): void;
/** A writable property and index signature typed `any`. */
export declare const box: { x: any };
export declare const dict: { [key: string]: any };
/** A generic argument `any` at an input, directly and through heritage. */
export interface Sink<T> {
  put(x: T): void;
}
export declare const sink: Sink<any>;
export declare class Base<T> {
  put(x: T): void;
}
export declare class Derived extends Base<any> {}
/** A nested default and a conditional type's check holding `any`. */
export declare function made<T = { x: any }>(): T;
export declare const conditional: any extends infer U ? { x: U } : never;
/** An `any` four type arguments deep. */
export declare function nestedArray(): any[][][][];

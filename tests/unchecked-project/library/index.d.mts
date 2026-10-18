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

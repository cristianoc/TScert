/* External declarations whose meaning the shadow program changes: see
 * WORK.md, "The any check over external declarations". */
export declare class B { m(x: any): void }
export declare class D extends B { m(x: number): void }
export declare function f(x: B): number;
export declare function f(x: D): string;
type A = any;
export declare const box: { x: A["missing"] };
export declare const chosen: any extends string ? string : number;
export interface Sink<T = any> {
  put(x: T): void;
}
export declare const sink: Sink;

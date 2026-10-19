// Read by tests/compiler-api-shapes.mts, never run: forms only a
// declaration file has.
export as namespace Library;
export declare function overloaded(a: string): string;
export declare function overloaded(a: number): number;
export declare class Declared { private constructor(); static readonly instance: Declared; }
export declare const unique: unique symbol;
declare module "*.css" { const text: string; export default text; }
export {};

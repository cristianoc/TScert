// Project globals spelling the evaluator's generated names
// (`imports-project/generated-names.d.ts`), beside an application it
// evaluates.
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<{ a: number }, "a"> }): "z" {
  return x;
}

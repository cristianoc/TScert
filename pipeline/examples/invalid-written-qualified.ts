// A qualified application keeps its bound: `Record`'s key `any`, read as
// `unknown`, is no `keyof any`.
export function f(x: keyof { a: globalThis.Record<any, number> }): "a" {
  return x;
}

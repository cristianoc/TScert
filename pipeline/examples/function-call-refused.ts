// A `Function` has no known signature: calling it cannot be checked, and a
// class value it may be throws when called. TypeScript allows the call at
// `any`.
function call(f: Function): unknown {
  return f();
}

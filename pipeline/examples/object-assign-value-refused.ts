// `Object.assign` is a call form: read as a value it would reach the copy
// with operands no rule checks (COMPILER-API.md, "First-class library
// values").
export function f(): number {
  const assign = Object.assign;
  return 0;
}

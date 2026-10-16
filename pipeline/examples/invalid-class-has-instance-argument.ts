// `instanceof` passes its operand to the static `[Symbol.hasInstance]`,
// whose parameter it must meet: here the method reads a field the operand
// need not have (TypeScript rejects the test too).
class HasValue {
  static [Symbol.hasInstance](x: { value: number }): boolean {
    return x.value.toFixed(0) === "0";
  }
}

export function argument(x: { other: number }): boolean {
  // @ts-expect-error the operand does not meet the method's parameter
  return x instanceof HasValue;
}

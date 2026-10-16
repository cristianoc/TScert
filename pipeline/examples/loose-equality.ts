// Primitive unions exercise every pair through the checked loose-equality operator.
type Primitive = string | number | bigint | boolean | symbol | null | undefined;

function samePrimitive(left: Primitive, right: Primitive): boolean {
  return left == right;
}

function differentPrimitive(left: Primitive, right: Primitive): boolean {
  return left != right;
}

function platform(value: string | undefined): "native" | "wasm" {
  return value == "native" ? "native" : "wasm";
}

function namedNullish(value: unknown, nil: null | undefined): boolean {
  return value == nil;
}

function namedNullishReversed(value: unknown, nil: null | undefined): boolean {
  return nil != value;
}

function evaluatedOperands(
  box: { value: number },
  right: number | string,
): boolean {
  return (box.value = box.value + 1) == right;
}

function sameRecord(
  left: { value: number },
  right: { value: number },
): boolean {
  return left == right;
}

function differentArrays(left: number[], right: readonly number[]): boolean {
  return left != right;
}

function arrayOrNullish(
  left: number[] | null,
  right: number[] | undefined,
): boolean {
  return left == right;
}

function functionAndRecord(
  left: (() => void) | { value: number },
  right: { value: number },
): boolean {
  return left == right;
}

function readonlyIdentity(
  left: readonly number[],
  right: readonly number[],
): boolean {
  return left == right;
}

function genericPrimitive<T extends Primitive>(left: T, right: T): boolean {
  return left != right;
}

function looseTypeof(value: number | string): number {
  if (typeof value == "number") return value;
  return 0;
}

function reversedLooseTypeof(value: number | string): string {
  if ("string" != typeof value) return "other";
  return value;
}

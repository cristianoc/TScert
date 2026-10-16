/**
 * Arithmetic on numbers: the double operation on two operands the number
 * test answers for, yielding the number family and never a singleton. A
 * compound assignment or an increment evaluates its target's parts once,
 * reads the current value at the storage contract, and writes the result
 * back; a postfix increment is the old value.
 */
/** A sum of two numbers, and of a sum and a literal. */
function sum(a: number, b: number): number {
  const c = a + b;
  return c - 1;
}
/** A compound assignment to a mutable local. */
function plusLocal(count: number): number {
  let total = count;
  total += 1;
  return total;
}
/** A compound assignment to a field, then a read of it. */
function plusField(box: { value: number }): number {
  box.value *= 2;
  return box.value;
}
/** A postfix increment of a field is the old value. */
function increment(): number {
  const box: { value: number } = { value: 0 };
  const old = box.value++;
  return old + box.value;
}
/** The computed key's effect happens once, before the read and the write. */
function annotatedCompoundKey(): number {
  const box: { value: number } = { value: 1 };
  let count = 0;
  box[(count += 1) === 1 ? "value" : "value"] += 1;
  return count;
}
/** A postfix increment of an element access. */
function computedUpdate(): number {
  const box: { value: number } = { value: 0 };
  let count = 0;
  return box[(count += 1) === 1 ? "value" : "value"]++;
}

/** Equality merges the zeros; arithmetic must retain their sign. */
function signedZero(): boolean {
  const z = 0 * (0 - 1);
  return 1 / (1 / z + 1 / 0) === 0;
}
/** Literal type zero includes both signed runtime zeros. */
function negativeZeroLiteral(): 0 {
  return -0;
}
function zeroParameter(value: 0): number {
  return 1 / value;
}

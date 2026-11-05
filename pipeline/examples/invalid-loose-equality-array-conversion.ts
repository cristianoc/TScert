// Array-to-primitive conversion can call an own valueOf method.
function arrayConversion(value: number[] | number, other: number): boolean {
  return value == other;
}

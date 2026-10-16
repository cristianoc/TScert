// An intersection arm with no value adds nothing to its union: a number
// branded by a record is no value, so the parameter is a number.
interface Brand {
  readonly brand: symbol;
}

export function plain(value: number | (number & Brand)): number {
  return value + 1;
}

export function viaCallback(values: (number | (number & Brand))[]): number {
  return values.reduce((sum, value) => sum + value, 0);
}

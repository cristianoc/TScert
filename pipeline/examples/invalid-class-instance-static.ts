// A method reading its class's static field reads it at the field's type.
class Counter {
  static readonly label: string = "n";
  n: number = 0;
  next(): number {
    // @ts-expect-error a string is not a number
    return Counter.label;
  }
}

export function use(c: Counter): number {
  return c.next();
}

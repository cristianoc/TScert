function polymorphicUse(seed: boolean): boolean {
  const id = <T>(value: T): T => value;
  return id(seed);
}

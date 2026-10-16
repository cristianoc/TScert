function invalidBound(count: number): boolean {
  const id = <T extends boolean>(value: T): T => value;
  return id(count);
}

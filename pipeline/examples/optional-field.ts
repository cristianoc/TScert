function optionalRead(value: { field?: number }): number | undefined {
  return value.field;
}

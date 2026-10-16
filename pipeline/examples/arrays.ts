function arrayWrite(items: number[]): number | undefined {
  items[0] = 2;
  return items[0];
}
function inferredArray(seed: number): number | undefined {
  const items = [seed];
  return items[0];
}
function optionalTuple(pair: [number, string?]): string | undefined {
  return pair[1];
}

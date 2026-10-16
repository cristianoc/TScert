function corruptArray(items: number[]): number | undefined {
  items[0] = "bad";
  return items[0];
}

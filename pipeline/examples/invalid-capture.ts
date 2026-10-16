function invalidCapture(seed: boolean): () => boolean {
  let value: boolean | null = seed;
  const read = (): boolean => value;
  value = null;
  return read;
}

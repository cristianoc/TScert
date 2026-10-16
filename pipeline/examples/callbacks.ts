function callback(seed: boolean): boolean {
  const choose = (left: boolean, right: boolean): boolean => left;
  return choose.call(null, seed, false);
}
function returnedCallback(seed: boolean): () => boolean {
  const saved = seed;
  return (): boolean => saved;
}
function capturedStorage(seed: boolean): () => boolean | null {
  let value: boolean | null = seed;
  const read = (): boolean | null => value;
  value = null;
  return read;
}
function acceptsCallback(f: (x: boolean) => boolean, seed: boolean): boolean {
  return f(seed);
}
function contravariantCallback(seed: boolean): boolean {
  const wide = (x: boolean): boolean => x;
  const narrow: (x: true) => boolean = wide;
  return narrow(true);
}

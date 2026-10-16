function functionFields(seed: boolean): boolean {
  const f = Object.assign<
    (x: boolean) => boolean,
    { value: boolean; ready: boolean }
  >((x: boolean): boolean => x, { value: seed, ready: true });
  f.value = false;
  return f.call(null, f.value);
}

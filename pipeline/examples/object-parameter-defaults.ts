interface Options {
  path?: string;
}

export function named(options: Options = {}): string | undefined {
  return options.path;
}

export function spread(options: Options = { ...{} }): string | undefined {
  return options.path;
}

export function closure(seed: string): string | undefined {
  const read = (options: { path?: string } = {}): string | undefined =>
    options.path;
  return read({ path: seed });
}

export function nested(
  options: { inner: { path?: string }; path?: string } = { inner: {} },
): string | undefined {
  return options.inner.path;
}

// `import.meta.dirname` is absent where the module is not loaded from a
// `file:` URL: a `data:` module reads `undefined`, which is no string.
export function directory(): string {
  return import.meta.dirname;
}

// A resolve hook that throws an error coded ERR_MODULE_NOT_FOUND has its
// `url` returned by `import.meta.resolve`, whatever value it holds.
export function located(specifier: string): string {
  return import.meta.resolve(specifier);
}

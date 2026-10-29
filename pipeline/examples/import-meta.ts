// Node's `import.meta` at the members the repository's code reads, each at
// `unknown`: `url`, which the module's wrapper may hold at any value;
// `dirname` and `filename`, present for a module loaded from a `file:` URL;
// `resolve`, called with a specifier, whose result a resolve hook may choose.
// A use as a string checks it first.
export function where(): string {
  const url = import.meta.url;
  if (typeof url !== "string") throw Error("the module's url is not a string");
  return url;
}
export function directory(): string {
  const dirname = import.meta.dirname;
  if (typeof dirname !== "string") throw Error("the module is not loaded from a file");
  return dirname;
}
export function file(): unknown {
  return import.meta.filename;
}
export function located(specifier: string): unknown {
  return import.meta.resolve(specifier);
}

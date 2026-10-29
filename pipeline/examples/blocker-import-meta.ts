// Module metadata: `import.meta.url`, a value at `unknown`, checked to be a
// string where the module uses it as one.
// Census functions:
// family-activation.mts#installationRoot, family-activation.mts#installations.
export function use(): string {
  const url = import.meta.url;
  if (typeof url !== "string") throw Error("the module's url is not a string");
  return url;
}

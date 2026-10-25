// Module metadata needs a source expression and its contract.
// Census functions:
// family-activation.mts#installationRoot, family-activation.mts#installations.
export function use(): string {
  return import.meta.url;
}

// Census functions: compiler-channel.mts#current,#identify,#launcher,#profile,
// #useInstallationForTests. A fresh identity record crosses a written union.
function identify(
  available: boolean,
):
  | { identity: { [field: string]: string | boolean }; unobserved?: never }
  | { unobserved: string } {
  if (!available) return { unobserved: "missing compiler" };
  return { identity: { path: "compiler", caseSensitive: true } };
}
export function current(available: boolean): string {
  return JSON.stringify(identify(available));
}

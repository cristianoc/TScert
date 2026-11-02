// Census functions: compiler-channel.mts#current,#identify,#launcher,#profile,
// #useInstallationForTests. A fresh identity record crosses a written union.
type Json = null | boolean | number | string | readonly Json[] | JsonObject;
type JsonObject = { readonly [key: string]: Json };
type Identification<T> = (
  | { identity: T; unobserved?: never }
  | { unobserved: string }
) &
  JsonObject;
function identify(
  available: boolean,
): Identification<{ [field: string]: string | boolean }> {
  if (!available) return { unobserved: "missing compiler" };
  return { identity: { path: "compiler", caseSensitive: true } };
}
export function current(available: boolean): string {
  return JSON.stringify(identify(available));
}

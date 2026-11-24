// A generic call returned by a callback passed to another generic call
// takes no hint from the outer call's binder, still unbound while the
// callback is walked: `fresh` is instantiated at its own actual's result.
// Census functions:
// files.mts#resolveObserved, files.mts#nodeResolve.
function fresh<T>(run: () => T): T {
  return run();
}
function outer<T>(run: () => T): T {
  return run();
}
function observe(s: string): boolean {
  return s.length > 0;
}
export function f(s: string): boolean {
  const before = outer(() => fresh(() => observe(s)));
  return before;
}

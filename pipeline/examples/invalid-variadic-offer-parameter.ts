// A closure binding a position a variadic signature may leave unwritten:
// `onNames` may call its listener with no names, so `name` would be
// undefined. TypeScript accepts it; the code binds a parameter past the
// signature's fixed ones, so it is not created at that signature.
function onNames(listener: (...names: string[]) => void): void {
  listener();
}
export function register(): void {
  const greet = (name: string): string => name;
  onNames(greet);
}

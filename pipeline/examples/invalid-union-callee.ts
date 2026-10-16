// Whichever arm the value is is called: the string arm does not take 1.
function either(
  f: ((x: number) => string) | ((y: string) => boolean),
): string | boolean {
  return f(1);
}

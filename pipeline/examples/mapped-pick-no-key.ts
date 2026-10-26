// `Pick` at no key is `{}`: every value but null and undefined.
export function make(): Pick<{ a: number }, never> {
  return 1;
}

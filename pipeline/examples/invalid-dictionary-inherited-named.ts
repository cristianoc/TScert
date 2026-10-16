// A dictionary literal owns no `__defineGetter__`: a read under that name
// finds the member every object inherits from `Object.prototype`, a
// function, where the dictionary's type says a number or nothing.
export function named(): number {
  const d: { [k: string]: number } = {};
  return d.__defineGetter__ ?? 0;
}

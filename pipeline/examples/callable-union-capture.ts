// A union of functions, captured by a closure and called there: every
// alternative accepts the argument, and the result is the union of the
// alternatives' results.

type Choice = ((unit: null) => true) | ((unit: null) => false);

function invoke(f: Choice): boolean {
  const run = (unit: null): boolean => f(unit);
  return run(null);
}

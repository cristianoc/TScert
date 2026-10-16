/**
 * Generic bodies that copy T: a const alias, and the first of two parameters.
 * These are not `return x` of a single parameter.
 */
function bind<T>(x: T): T {
  const y: T = x;
  return y;
}

function fst<T>(x: T, y: T): T {
  return x;
}

// Distinct parameters cannot be identified just because both are unconstrained.
function second<T, U>(x: T, y: U): U {
  return y;
}

// Dependent bounds are directed inclusions, including through a const annotation.
function upper<T, U extends T>(x: U): T {
  const y: T = x;
  return y;
}

// Follow several declared bounds without replacing a parameter by its bound.
function boundChain<T extends boolean, U extends T, V extends U>(
  x: V,
): boolean {
  return x;
}

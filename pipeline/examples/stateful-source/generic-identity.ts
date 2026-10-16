/**
 * Generic identity under a rigid type parameter. The body is checked once
 * for every admissible T; this is not a concrete instantiation.
 */
function id<T>(x: T): T {
  return x;
}

// A declaration file named like a standard library file, outside the
// project that reads it: the compiler's library resolution does not give
// it, so it is no part of the standard library.
interface ObjectConstructor {
  assign(n: number): string;
}

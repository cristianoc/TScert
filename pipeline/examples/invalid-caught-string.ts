// What a handler catches is `unknown`: anything may be thrown, by the body's
// own `throw` or by what it calls. It is not a string without a check.
function message(f: () => string): string {
  try {
    return f();
  } catch (e) {
    return e;
  }
}

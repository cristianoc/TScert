// Inside a generic body, a generic closure returning the body's binder at its
// own: the one call names U := T, which it would meet, but the code is checked
// at every U.
function nestedWrong<T>(value: T): T {
  const bad = <U>(first: T, second: U): U => first;
  return bad(value, value);
}

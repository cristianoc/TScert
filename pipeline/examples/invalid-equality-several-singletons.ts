// Where a field equals a name holding one of two singletons, it is either.
function eitherOne(o: { a: 0 | 1 | 2 }, x: 0 | 1): 0 {
  if (o.a === x) {
    return o.a;
  }
  return 0;
}

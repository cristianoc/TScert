// A record is not callable, so it is not a `Function`, even one TypeScript
// would accept for having `Function`'s members.
function bad(o: { a: number }): Function {
  return o;
}

// A body that reads its binder as a concrete type: `T` is below `boolean` at
// no instantiation it does not name, so the field's value is not a Boolean.
type Box<T> = { value: T };

function asBoolean<T>(b: Box<T>): boolean {
  return b.value;
}

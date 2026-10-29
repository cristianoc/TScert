// `Reflect.ownKeys` of a value typed `object`, which may be a host object:
// a host exotic object's [[OwnPropertyKeys]] may be the host's own code.
// Refused at the argument.
export function keys(o: object): (string | symbol)[] {
  return Reflect.ownKeys(o);
}

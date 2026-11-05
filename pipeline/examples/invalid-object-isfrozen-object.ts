// `Object.isFrozen` of a value typed `object`, which may be a host object: a
// host exotic object's [[IsExtensible]] and [[OwnPropertyKeys]] may be the
// host's own code. Refused at the argument.
export function frozen(o: object): boolean {
  return Object.isFrozen(o);
}

// A parameter property named `stack` assigns the instance's own `stack`
// after `super`, which stays non-enumerable, where the model would define an
// enumerable field. Refused at the parameter.
class Traced extends Error {
  constructor(public stack: string) {
    super("x");
  }
}

export function keys(): string[] {
  return Object.keys(new Traced("s"));
}

// A static block reading `this` reads the class value, whose statics are
// bindings of their own: refused.
class Registry {
  static readonly size: number = 3;
  static {
    const size = this.size;
  }
}

export function make(): Registry {
  return new Registry();
}

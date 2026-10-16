// A static initializer constructing its class whose construction reads a
// static field: the class's statics are defined one by one, so construction
// can read one not yet defined, `undefined` in JavaScript, where its type
// promises a number. Constructing a class in its static initializer is
// admitted only where construction reads no static field and runs no code.
class P {
  static readonly origin: P = new P();
  static readonly k: number = 1;
  v: number;
  constructor() {
    this.v = P.k;
  }
}

export function read(): number {
  return P.origin.v;
}

// A script without a "use strict" directive is sloppy code, whose call binds
// an object receiver unchanged and converts any other (the global object, a
// wrapper object). A function reading `this` whose receiver type holds
// objects only is called with objects only, so it binds them as strict code
// does: a declaration, a function expression, a literal's method, and an
// arrow capturing the receiver.
type Counter = { n: number };

function readsThis(this: Counter): number {
  return this.n;
}

function caller(): number {
  return readsThis.call({ n: 1 });
}

function viaExpression(c: Counter): number {
  const read = function (this: Counter): number {
    return this.n;
  };
  return read.call(c);
}

function viaMethod(): number {
  const o = {
    n: 2,
    get(this: Counter): number {
      return this.n;
    },
  };
  return o.get();
}

function viaArrow(c: Counter): number {
  const later = function (this: Counter): () => number {
    return () => this.n;
  };
  return later.call(c)();
}

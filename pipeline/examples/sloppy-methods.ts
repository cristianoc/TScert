// A script without a "use strict" directive is sloppy code. An object
// literal's methods that do not read `this` behave as strict ones do:
// sloppy code differs in what `this` is bound to, which they never observe.
function ordinaryMethods(): number {
  const x = {
    get(): number {
      return 1;
    },
    set(v: number): number {
      return v;
    },
  };
  return x.set(x.get());
}

// A script without a "use strict" directive is sloppy code. A literal's
// method without a `this` annotation accepts any receiver; called plainly, it
// is given `undefined`, which its sloppy call replaces by the global object:
// `count` reads the global object's `n`, `undefined`, where TypeScript types
// it `number`.
function count(): number {
  const o = {
    n: 1,
    get(): number {
      return (this as { n: number }).n;
    },
  };
  const get = o.get;
  return get();
}

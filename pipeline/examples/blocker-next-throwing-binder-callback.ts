// Census: tools/array-prototype.mts#functionPrototype,#mergeRefusal,#prototype.
type Scope = {
  named: () => Modifies<{ values: "any"; stores: "grow" }, number>;
};
export function scope(ok: boolean, failure: () => Error): Scope {
  return {
    named: () => {
      if (ok) return 1;
      throw failure();
    },
  };
}

// A class whose constructor takes fewer parameters than the construct
// signature it meets: `new` discards the extra actuals, so the class value is
// claimed at that signature beside its own, and its constructor's body is
// checked there, at the parameters it binds.
interface Shape {
  area(): number;
}

class Unit {
  area(): number {
    return 1;
  }
}

const makers: { readonly [name: string]: new (seed: number) => Shape } = {
  unit: Unit,
};

export function build(name: "unit" | "square"): number {
  const make = makers[name];
  return make === undefined ? 0 : new make(3).area();
}

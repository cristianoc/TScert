// A class offered a longer construct signature, read from a dictionary at a
// string key: a read at a string key known only at run time may find a member every
// object inherits from `Object.prototype`, and is refused (the offer itself is
// `class-constructor-offer-uninherited-key`'s).
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

export function build(name: string): number {
  const make = makers[name];
  return make === undefined ? 0 : new make(3).area();
}

// A computed key naming a `unique symbol` constant is that symbol's key: the
// literal owns it, as a type's computed key names it.
const key: unique symbol = Symbol();
export function make(): object {
  return { [key]: 1 };
}

export function read(): number {
  const o = { [key]: 2 };
  return o[key];
}

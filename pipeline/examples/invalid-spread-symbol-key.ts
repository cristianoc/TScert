// A spread copies an own enumerable symbol-keyed property too, which the
// copy the model states, at string keys only, does not say.
declare const tag: unique symbol;

export function copy(x: { [tag]: number }): { [tag]: number } {
  return { ...x };
}

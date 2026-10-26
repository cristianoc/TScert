// `"message" in e` on an error the source builds, whose message the model
// holds on the instance's first link: the key is refused for every operand,
// since an error built elsewhere without a message inherits it from
// `Error.prototype`, which the model does not hold. Under Node,
// `observed()` returns true.
class Kept extends Error {}

export function observed(): boolean {
  const e = new Kept("kept");
  return "message" in e;
}

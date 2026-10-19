// `super(null)`: `Error` converts the message by `ToString`, so it is
// `"null"` (run under Node), where `undefined` gives none. The argument is
// stated at `string | undefined`, and `null` is refused there.
class Nulled extends Error {
  constructor() {
    // @ts-expect-error a null message
    super(null);
  }
}

export function read(): string {
  return new Nulled().message;
}

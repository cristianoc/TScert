// `super(message, options)` reads `options.cause` through `[[Get]]`: the
// options are not stated, so the call is refused.
class Caused extends Error {
  constructor(m: string, cause: unknown) {
    super(m, { cause });
  }
}
export function read(): string {
  return new Caused("x", 1).message;
}

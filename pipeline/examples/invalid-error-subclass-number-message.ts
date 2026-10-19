// A number message would be converted by `ToString`, which may run code:
// the message is stated at `string | undefined`, and the number is refused.
class Coded extends Error {
  constructor(code: number) {
    // @ts-expect-error a number message
    super(code);
  }
}
export function read(): string {
  return new Coded(1).message;
}

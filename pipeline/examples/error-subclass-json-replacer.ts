// A replacer naming `message` serializes the message, through `[[Get]]`
// (run under Node: `{"message":"x"}`). The parameter is a JSON value, which
// the error, holding a prototype, is not.
class Decline extends Error {}
export function text(): string {
  return JSON.stringify(new Decline("x"), ["message"]);
}

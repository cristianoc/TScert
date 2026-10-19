// A destructuring assignment writing `stack`: the instance's own `stack`
// stays non-enumerable (run under Node). Refused at the target's receiver.
class Decline extends Error {}

export function traced(): string[] {
  const e = new Decline("x");
  [e.stack] = ["s"];
  return Object.keys(e);
}

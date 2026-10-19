// `Object.assign` onto an instance constructed without a message: the copied
// `message` becomes an own enumerable property (run under Node), with one it
// stays non-enumerable. Refused at the target, whose type admits an instance.
class Decline extends Error {}

export function relabelled(): string[] {
  const e = new Decline();
  Object.assign(e, { message: "z" });
  return Object.keys(e);
}

// `hasOwnProperty("message")` is `true` of the error, whose stated message
// sits on a link it holds: the precise ownness observation is refused.
class Decline extends Error {}
export function own(): boolean {
  return new Decline("x").hasOwnProperty("message");
}

// A source whose type does not mention `message` may still own it:
// `Object.assign` copies it onto the instance, enumerable where none was
// passed (run under Node). Only a literal with its keys written is known to
// carry neither key, so the call is refused at the target.
class Decline extends Error {}

export function relabelled(): string[] {
  const full = { message: "z", tag: 1 };
  const hidden: { tag: number } = full;
  const e = new Decline();
  Object.assign(e, hidden);
  return Object.keys(e);
}

// `2^53` returned where `SafeInt` is declared: it lies past the safe
// integers, so the return is refused. The refusal is of the type contract,
// not of a run.
export function past(): SafeInt {
  return 9007199254740992;
}

// A field narrowed through one parameter, then the same key written through
// another parameter, which may hold the same object: a write keeps what is
// known of the other keys of its own object alone, so the narrowed field is
// read at its contract, `Context | null`, which holds the `null` written
// when the two parameters are one object.
type Context = { font: string };
type State = { context: Context | null; font: string };

export function aliased(state: State, other: State): Context {
  if (state.context === null) state.context = { font: "" };
  other.context = null;
  return state.context;
}

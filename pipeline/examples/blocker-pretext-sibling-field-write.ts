// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getWholeRunContext,
// measurement.ts#getFontKanaKerning.
// Refusal: reject: source expression obligation: no derivation of its
// return-contract claim.
// A field of a parameter's object narrowed by a test and a write, then a
// write of another field of the same object: a write keeps what is known of
// a location only where a separation fact states it apart from the written
// one, and none states two fields of an object the function did not
// allocate apart, so the first field is read at its contract.
type Context = { font: string };
type State = { context: Context | null; font: string };

function create(): Context {
  return { font: "" };
}

export function wholeRunContext(state: State, font: string): Context {
  if (state.context === null) state.context = create();
  state.font = font;
  return state.context;
}

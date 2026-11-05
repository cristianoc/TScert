// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): measurement.ts#getWholeRunContext,
// measurement.ts#getFontKanaKerning.
// A field of a parameter's object narrowed by a test and a write, then a
// write of another field of the same object: the written field's location
// belongs to its key alone, so the write keeps the first field's fact.
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

// An object whose field is an accessor reading another field: a write of the
// other field changes what the accessor answers, which the model's records,
// data properties only, cannot state. The fragment admits no accessor in a
// literal, and the caller contract states every field of a value at a
// structural type an own data property.
type Context = { font: string };
type State = { context: Context | null; font: string };

export function wholeRunContext(state: State, font: string): Context {
  if (state.context === null) return { font };
  state.font = font;
  return state.context;
}

export function run(): Context {
  const context: Context = { font: "a" };
  const state: State = {
    font: "",
    get context(): Context | null {
      return this.font === "b" ? null : context;
    },
    set context(value: Context | null) {},
  };
  return wholeRunContext(state, "b");
}

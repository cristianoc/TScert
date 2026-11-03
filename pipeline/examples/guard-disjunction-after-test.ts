// Guards' narrowings survive a disjunction whose first operand is a test:
// `(t || !g(a)) || !g(b)` is dispatched as `t || (!g(a) || !g(b))`, so where
// it is false both `a` and `b` are at the guarded type. Stands for the census
// function type-term.mts#deferredOf
// (`(form !== "keyof" && form !== "pick") || !isModifier(readonlyMod) || !isModifier(optionalMod) || …`).
type Modifier = "keep" | "add" | "remove";
const isModifier = (text: string | undefined): text is Modifier =>
  text === "keep" || text === "add" || text === "remove";
export function modifiers(name: string): [Modifier, Modifier] {
  const [form, readonlyMod, optionalMod, ...rest] = name.split(":");
  if (
    (form !== "keyof" && form !== "pick") ||
    !isModifier(readonlyMod) ||
    !isModifier(optionalMod) ||
    rest.length
  )
    throw Error(`a malformed name: ${name}`);
  return [readonlyMod, optionalMod];
}

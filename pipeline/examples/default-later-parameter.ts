// JavaScript throws even when the later actual is provided. Raw actual slots
// do not make later parameter bindings initialized while a default runs.
function laterDefault(): boolean | undefined {
  const pick = (
    first: boolean | undefined = second,
    second?: boolean,
  ): boolean | undefined => first;
  return pick(undefined, true);
}

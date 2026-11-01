// Census functions:
// files.mts#observed
// files.mts#observedNoting
// files.mts#remembered
// files.mts#nodeResolve
// files.mts#resolveObserved
type Noted = { observation: string; node: boolean };
export function observed<T>(
  run: () => T,
  answers: Map<string, Noted>,
): { value: T; noted: Noted[] } {
  let value: T;
  try {
    value = run();
  } finally {
    answers.delete("");
  }
  const noted = [...answers.values()].sort((a, b) =>
    a.observation < b.observation ? -1 : 1,
  );
  return { value, noted };
}

// Cache callback returning a record whose answer is a real path or null.
// Census functions:
// files.mts#answerOf
// files.mts#observationsHold
// files.mts#validateLedger
// files.mts#realOf
// files.mts#compilerFileSystem
// files.mts#findPackage
// files.mts#observeScope
// files.mts#observeResolution
// files.mts#loadModule
function cached<R extends { readonly answer: string | null }>(
  answers: Map<string, R>,
  key: string,
  read: () => R,
): R {
  const known = answers.get(key);
  const result = known ?? read();
  if (!known) answers.set(key, result);
  return result;
}
export function real(
  answers: Map<string, { answer: string | null }>,
  path: string,
): string | null {
  return cached(answers, path, () => {
    try {
      return { answer: path };
    } catch {
      return { answer: null };
    }
  }).answer;
}

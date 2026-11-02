// Census: tools/files.mts#nodeResolve,#resolveObserved.
type Observation = readonly [string, string, string | null];
type Noted = { observation: Observation; node: boolean };
export function same(before: Noted[], after: Noted[]): boolean {
  return JSON.stringify(before) === JSON.stringify(after);
}

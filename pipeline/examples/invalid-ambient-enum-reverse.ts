// An ambient enum is the environment's object, of which its members alone
// are assumed: the environment may supply one without the reverse mapping
// TypeScript's index signature promises.
declare enum Grade {
  Low = 0,
  High = 1,
}
declare const Grede: { readonly Low: 0; readonly High: 1; readonly 0: string };
function lowName(): number {
  return Grade[0].length;
}
function shadowName(): number {
  return Grede[0].length;
}

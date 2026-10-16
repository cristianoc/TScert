// `Number` both called and read through its members: each use is admitted
// alone (`library-number-call`, `library-number-tests`), but together the
// global is a callable object with methods, a type the claims have no
// clause for.
function parse(text: string): number {
  const n = Number(text);
  return Number.isFinite(n) ? n : 0;
}

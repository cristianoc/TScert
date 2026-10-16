// `typeof x` of a constant whose literal has a method is the type
// TypeScript infers for it, which no term of the fragment states: an
// inferred method is not read.
const origin = {
  x: 0,
  get(): number {
    return 1;
  },
};
export function copy(p: typeof origin): number {
  return p.x;
}

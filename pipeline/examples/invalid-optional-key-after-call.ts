// A key found present stays present, but what it holds may change: a call
// between the test and the read may write `undefined` there.
function afterCall(x: { f?: number | undefined }, g: () => void): number {
  if (x.f !== undefined) {
    g();
    return x.f;
  }
  return 0;
}

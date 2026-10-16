// JavaScript gives a block's declared name to the declaration from the start
// of its block: the closure reads the local, a string, once it is
// initialized, never the module's number. A mention before the declaration is
// refused.
const seed: number = 1;
function capturedEarly(): string {
  const read = () => seed;
  const seed: string = "local";
  return "" + read();
}

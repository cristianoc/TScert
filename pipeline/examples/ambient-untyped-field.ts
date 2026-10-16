// A field an ambient class declares without a type, which TypeScript reads
// at `any`, is read at `unknown` and never written.
declare class Untyped {
  pub;
  known: number;
}
function passThrough(x: Untyped): Untyped {
  return x;
}
function readAsUnknown(x: Untyped): unknown {
  return x.pub;
}
function readKnown(x: Untyped): number {
  return x.known;
}
declare class Secret<T> {
  secret;
}
declare function secret<T>(): Secret<T>;
function sharedAcrossArguments(): Secret<number> {
  return secret<string>();
}

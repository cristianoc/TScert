// A mutable index signature is a writable index: every present value's
// location holds exactly its contract. It reads as a readonly one does, and
// it is a readonly one.
function makeEmpty(): { [key: string]: boolean } {
  return {};
}

function makeDictionary(): { [key: string]: boolean } {
  return { ready: true, done: false };
}

function retain(x: { [key: string]: boolean }): { [key: string]: boolean } {
  return x;
}

function asView(x: { [key: string]: boolean }): {
  readonly [key: string]: boolean;
} {
  return x;
}

function read(x: { [key: string]: boolean }, key: string): boolean | undefined {
  return x[key];
}

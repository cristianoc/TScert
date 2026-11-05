// A mutable string dictionary read at a string key: a read at a string key known only at run time may find a member every
// object inherits from `Object.prototype`, and is refused.
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

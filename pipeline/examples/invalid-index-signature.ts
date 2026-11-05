// A readonly string dictionary read at a string key: a read at a string key known only at run time may find a member every
// object inherits from `Object.prototype`, and is refused.
function retainDictionary(x: { readonly [key: string]: boolean }): {
  readonly [key: string]: boolean;
} {
  return x;
}

function readPossiblyAbsent(x: {
  readonly [key: string]: boolean;
}): boolean | undefined {
  return x["missing"];
}

// All locations are allocated here, so every present value can be checked.
function makeDictionary(): { readonly [key: string]: boolean } {
  return { ready: true, done: false };
}

// The key is evaluated at runtime; its value is not a known string singleton.
function readDynamic(
  x: { readonly [key: string]: boolean },
  key: string,
): boolean | undefined {
  return x[key];
}

// A required named view and a string index constrain the same object.
function preserveMixed(x: {
  readonly ready: boolean;
  readonly [key: string]: boolean;
}): {
  readonly ready: boolean;
  readonly [key: string]: boolean;
} {
  return x;
}

// The computed key can still miss, despite the required named field.
function readMixed(
  x: { readonly ready: boolean; readonly [key: string]: boolean },
  key: string,
): boolean | undefined {
  return x[key];
}

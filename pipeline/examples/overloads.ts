// One closure advertising two signatures. Each is a separate obligation on the
// same body, and the producer states what that body claims under each.
// TypeScript rejects the assignment: it checks the implementation's declared
// signature against each member rather than re-checking the body, so
// `(x: boolean | null) => boolean | null` is not assignable to
// `(x: boolean) => boolean`. The verifier checks the body under each signature
// and both hold, which is why this witness is the OCaml producer's alone.
function guardedOverload(seed: boolean): boolean {
  const pick: ((x: boolean) => boolean) & ((x: null) => null) = (
    x: boolean | null,
  ): boolean | null => {
    if (x === null) {
      return null;
    }
    return x;
  };
  return pick(seed);
}
function overloadAtNull(seed: boolean): null {
  const pick: ((x: boolean) => boolean) & ((x: null) => null) = (
    x: boolean | null,
  ): boolean | null => {
    if (x === null) {
      return null;
    }
    return x;
  };
  const chosen: boolean = pick(seed);
  const done: null = pick(null);
  return chosen ? done : done;
}

// Each signature retains the same captured storage contract. A row cannot
// invent a stronger current-content assertion for that captured location.
function overloadCapture(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const pick: ((x: boolean) => boolean) & ((x: null) => null) = (
    x: boolean | null,
  ): boolean | null => {
    if (x === null) {
      return null;
    }
    return cell.value;
  };
  return pick(seed);
}

/** Undefined is a distinct singleton, including at a function boundary. */
function undefinedIdentity(value: undefined): undefined {
  return value;
}

/** All four primitive values remain represented in a union. */
function undefinedUnion(
  value: null | boolean | undefined,
): null | boolean | undefined {
  return value;
}

/** A write through an alias must permit undefined in the storage invariant. */
function undefinedAlias(value: boolean | undefined): boolean | undefined {
  const cell: { value: boolean | undefined } = { value: value };
  const alias: { value: boolean | undefined } = cell;
  alias.value = undefined;
  return cell.value;
}

/** Both arrow operands include undefined; neither may be silently projected. */
function undefinedCallback(value: boolean | undefined): boolean | undefined {
  const identity: (x: boolean | undefined) => boolean | undefined = (
    x: boolean | undefined,
  ): boolean | undefined => x;
  return identity(value);
}

/** Coalescing handles both nullish values, but preserves false. */
function undefinedCoalesce(value: null | boolean | undefined): boolean {
  return value ?? false;
}

/** A strict undefined test justifies the following statement's Boolean claim. */
function undefinedBranch(value: boolean | undefined): boolean {
  if (value === undefined) {
    return false;
  }
  return value;
}

/** The reversed comparison must observe the same value and polarity. */
function reversedUndefined(value: boolean | undefined): boolean {
  if (undefined !== value) {
    return value;
  }
  return false;
}

/** Testing for null must leave undefined on the other edge. */
function nullIsDifferent(value: null | undefined): undefined {
  if (value === null) {
    return undefined;
  }
  return value;
}

/** Undefined guards work inside ordinary compositional closure proofs too. */
function undefinedClosure(value: boolean | undefined): boolean {
  const present: (x: boolean | undefined) => boolean = (
    x: boolean | undefined,
  ): boolean => (x === undefined ? false : x);
  return present(value);
}

/** Only the nullish branch executes the fallback, which mutates a captured cell. */
function undefinedFallback(value: boolean | undefined): boolean {
  const cell: { value: boolean } = { value: true };
  const fallback: (unit: null) => boolean = (unit: null): boolean => {
    cell.value = false;
    return true;
  };
  const selected: boolean = value ?? fallback(null);
  return cell.value;
}

/** A later current-undefined claim can be justified by this direct write. */
function undefinedCurrent(seed: boolean): boolean | undefined {
  const cell: { value: boolean | undefined } = { value: seed };
  cell.value = undefined;
  return cell.value;
}

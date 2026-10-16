/** A shape guard selects an existing signature from several runtime shapes. */
function guardedShape(
  f: ((flag: boolean, unit: null) => boolean) | boolean | null,
  other: ((flag: boolean, unit: null) => boolean) | boolean | null,
  flag: boolean,
): boolean {
  if (typeof f === "function") {
    return f(flag, null);
  }
  return false;
}

/** A returning negative guard narrows an immutable capture for a returned thunk. */
function capturedShape(
  f: ((flag: boolean, unit: null) => boolean) | boolean | null,
  flag: boolean,
): () => boolean {
  const candidate = f;
  if ("function" !== typeof candidate) {
    return (): boolean => false;
  }
  return (): boolean => candidate(flag, null);
}

/** The operand is an effectful call, evaluated once as a Boolean value test.
 * Its result does not give the factory a narrower result signature. */
function shapeOfResult(
  factory: () => ((flag: boolean) => boolean) | null,
): boolean {
  return typeof factory() === "function";
}

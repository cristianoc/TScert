// Scopes, branch arms and parameter slots as the lowering places them, pinned
// by singleton types: a lowering that resolved a name to another slot, let a
// branch-local binding reach an outer one, refined another binding than the
// one tested, or started a parameter's cell with another argument would not
// verify.

/** A later binding leaves an earlier name at its own slot. */
function olderSlot(): true {
  const x = true;
  const y = false;
  return x;
}

/** Each arm's binding of one name stays in its arm. */
function branchLocals(q: boolean): true {
  const outer = true;
  if (q) {
    const local = false;
    return outer;
  } else {
    const local = null;
    return outer;
  }
}

/** A guard refines the binding it tests, which is older than a later local. */
function refinesOlder(q: boolean): boolean {
  const tested: boolean = q;
  const other: boolean = false;
  if (tested) {
    const t: true = tested;
    return t;
  }
  const f: false = tested;
  return f;
}

/** Parameters take their slots in declaration order. */
function parameterSlots(first: null, second: true): true {
  return second;
}

/** Each assigned parameter's cell starts with its own argument; an
 * unassigned parameter between them stays a value. */
function assignedParameters(x: true, keep: null, z: false): null {
  const seenX: true = x;
  const seenZ: false = z;
  x = seenX;
  z = seenZ;
  return keep;
}

/** `??=` reads its target once and evaluates the assignment only on the
 * nullish arm. */
function nullishFallback(x: boolean | null): boolean {
  return (x ??= true);
}

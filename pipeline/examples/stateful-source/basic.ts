/**
 * Widen a true singleton to boolean while copying a local. The initializer and
 * declared binding type are checked separately.
 */
function copyTrue(): boolean {
  const x: true = true;
  const y: boolean = x;
  return y;
}

/**
 * Preserve an inferred false singleton through a local binding and return.
 */
function copyFalse(): false {
  const x = false;
  return x;
}

/**
 * Place null in a union-annotated binding. The union permits this value
 * without requiring a value from every member.
 */
function nullOrBoolean(): null | boolean {
  const x: null | boolean = null;
  return x;
}

/**
 * Read an older local after introducing another binding. This exercises
 * lexical slot identity during lowering.
 */
function keepOlderBinding(): true {
  const x: true = true;
  const y: false = false;
  return x;
}

/**
 * Join two arms with different local scopes. Both incoming edges must justify
 * the shared continuation, where only outer remains in scope.
 */
function mergeWithLocals(): true {
  const outer: true = true;
  if (true) {
    const local: false = false;
    const another: null = null;
  } else {
    const local: null = null;
  }
  return outer;
}

/**
 * Give each arm its own return. No shared continuation is needed when both
 * arms terminate.
 */
function bothReturn(): boolean {
  if (false) {
    return true;
  } else {
    return false;
  }
}

/**
 * Join nested falling-through branches while dropping their local bindings.
 * The outer null binding must survive every scope change.
 */
function nestedMerge(): null {
  const outer: null = null;
  if (true) {
    const local: boolean = false;
    if (false) {
      const inner: true = true;
    }
  }
  return outer;
}

/**
 * Return from one arm and continue on the other. Only the falling-through path
 * reaches the final return.
 */
function earlyArm(): boolean {
  const outer: false = false;
  if (false) {
    return true;
  }
  return outer;
}

/**
 * Use a Boolean test to justify true and false claims for the tested immutable
 * local in the corresponding arms.
 */
function narrowVariable(): boolean {
  const condition: boolean = true;
  const other: boolean = false;
  if (condition) {
    const yes: true = condition;
    return yes;
  } else {
    const no: false = condition;
    return no;
  }
}

/**
 * Refine a local separately in each arm, then rejoin at its Boolean type.
 * Branch-specific singleton facts must not leak across the join.
 */
function refineThenMerge(): boolean {
  const condition: boolean = false;
  if (condition) {
    const yes: true = condition;
  } else {
    const no: false = condition;
  }
  return condition;
}

/**
 * Select the second of two parameters and copy it. This checks that parameter
 * names resolve to the correct input slots.
 */
function selectParameter(first: null, second: boolean): boolean {
  const copy: boolean = second;
  return copy;
}

/**
 * Refine a Boolean parameter on both edges of a test while retaining a
 * separate null parameter.
 */
function narrowParameter(condition: boolean, value: null): boolean {
  if (condition) {
    const yes: true = condition;
    return yes;
  } else {
    return condition;
  }
}

/**
 * Keep an unrelated parameter unchanged while the tested parameter is refined
 * differently in each arm.
 */
function parameterMerge(condition: boolean, value: null): null {
  if (condition) {
    const yes: true = condition;
  } else {
    const no: false = condition;
  }
  return value;
}

/**
 * Require true at the function boundary and preserve that exact result. The
 * input contract is independent of internal point claims.
 */
function singletonParameter(exact: true): true {
  return exact;
}

/**
 * Accept and return any null-or-Boolean value. No branch test or narrowing is
 * necessary for an identity function.
 */
function unionParameter(value: null | boolean): null | boolean {
  return value;
}

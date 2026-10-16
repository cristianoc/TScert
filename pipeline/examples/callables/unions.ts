// A closure's null guard must retain both possible callable results.
function guardedCallableUnion(
  f: ((unit: null) => true) | ((unit: null) => false) | null,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    f === null ? false : f(unit);
  return invoke(null);
}

/**
 * The right side of && runs only when the captured value is callable. The
 * call returns true, but skipping it produces false.
 */
function andGuardedCallable(f: ((unit: null) => true) | null): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    f !== null && f(unit);
  return invoke(null);
}

/**
 * The right side of || runs only after the null test fails. A null input
 * returns true without invoking anything.
 */
function orGuardedCallable(f: ((unit: null) => false) | null): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    f === null || f(unit);
  return invoke(null);
}

// Coalescing selects a function before invocation; either signature can supply
// the result, and both null and undefined must select the fallback.
function coalescedCallable(
  f: ((unit: null) => true) | null | undefined,
  fallback: (unit: null) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    (f ?? fallback)(unit);
  return invoke(null);
}

/**
 * Return a closure after guarding its immutable capture. The non-null branch
 * retains both callable alternatives for later invocations; the null branch
 * returns a separate closure that never calls the captured value.
 */
function capturedGuardedCallable(
  f: ((unit: null) => true) | ((unit: null) => false) | null,
): (unit: null) => boolean {
  if (f === null) {
    return (unit: null): boolean => false;
  } else {
    return (unit: null): boolean => f(unit);
  }
}

/**
 * Select an immutable callable alias inside a closure, then capture that alias
 * in another closure. A later call must respect either selected signature;
 * selecting the fallback does not make the original nullable input callable.
 */
function aliasedCallableSelection(
  f: ((unit: null) => true) | null,
  fallback: (unit: null) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean => {
    const selected = f === null ? fallback : f;
    const call: (arg: null) => boolean = (arg: null): boolean => selected(arg);
    return call(unit);
  };
  return invoke(null);
}

/**
 * Both possible callees accept true, although only one accepts false. The
 * selected function can be called at the shared domain, and its result must
 * cover both alternatives.
 */
function sharedCallableDomain(
  choose: boolean,
  wide: (value: boolean) => true,
  narrow: (value: true) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean => {
    const selected = choose ? wide : narrow;
    return selected(true);
  };
  return invoke(null);
}

/**
 * Calls inside the conditional retain the tested Boolean's branch refinement.
 * The true branch can pass it to the true-only callee; the false branch needs
 * the wider Boolean domain. Both singleton call results reach the join.
 */
function branchLocalCallableDomains(
  choose: boolean,
  wide: (value: boolean) => true,
  narrow: (value: true) => false,
): boolean {
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    choose ? narrow(choose) : wide(choose);
  return invoke(null);
}

/**
 * A call's argument writes the captured cell before the callee reads it. The
 * assignment supplies its RHS as the argument; the captured read retains the
 * cell's Boolean invariant.
 */
function callableArgumentWrite(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const read: (value: boolean) => boolean = (value: boolean): boolean =>
    cell.value;
  const result: boolean = read((cell.value = false));
  return result;
}

/**
 * A nested call writes an outer captured cell through its argument. Saving the
 * write receiver and RHS introduces temporary bindings around the named
 * parameter is evaluated; those bindings must not change what the names refer to.
 */
function nestedCallableArgumentWrite(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const read: (value: boolean) => boolean = (value: boolean): boolean =>
    cell.value;
  const invoke: (next: boolean) => boolean = (next: boolean): boolean =>
    read((cell.value = next));
  return invoke(false);
}

/**
 * A factory's branch returns a closure after narrowing its own argument.
 * The escaping closure retains that immutable capture after the factory ends;
 * the null branch contributes a separate false-returning implementation.
 */
function branchReturnedCapture(seed: boolean | null): boolean {
  // prettier-ignore
  const make: (input: boolean | null) => (unit: null) => boolean =
    (input: boolean | null): (unit: null) => boolean => {
      if (input === null) {
        return (unit: null): boolean => false;
      } else {
        return (unit: null): boolean => input;
      }
    };
  const read = make(seed);
  return read(null);
}

/**
 * A Boolean-accepting closure and a true-only closure can both implement the
 * factory's true-only result contract. Returning the broader implementation in
 * one branch does not let callers pass false to the joined result.
 */
function returnedCallableDomain(flag: boolean): boolean {
  // prettier-ignore
  const make: (choose: boolean) => (next: true) => boolean =
    (choose: boolean): (next: true) => boolean => {
      if (choose) {
        return (next: boolean): boolean => next;
      } else {
        return (next: true): boolean => false;
      }
    };
  const invoke = make(flag);
  return invoke(true);
}

/**
 * A factory may decline to produce a closure. Its nullable result survives the
 * call and must be guarded independently of the Boolean argument supplied to
 * the factory; the returned closure captures that particular argument.
 */
function nullableFactoryResult(flag: boolean): boolean {
  const make: (enabled: boolean) => ((unit: null) => boolean) | null = (
    enabled: boolean,
  ): ((unit: null) => boolean) | null => {
    if (enabled) {
      return (unit: null): boolean => enabled;
    } else {
      return null;
    }
  };
  const selected = make(flag);
  return selected === null ? false : selected(null);
}

/**
 * Separate nullable bindings have identical contracts. Guarding the first
 * does not refine the second; each callback needs its own null-test edge.
 */
function distinctNullableCallbacks(): boolean {
  const first: ((unit: null) => boolean) | null = (unit: null): boolean => true;
  const second: ((unit: null) => boolean) | null = (unit: null): boolean =>
    false;
  if (first === null) {
    return false;
  }
  if (second === null) {
    return first(null);
  }
  return second(null);
}

/**
 * A nullable local has a wider declaration than its initializer. Its null guard
 * must survive capture by a returned closure, without relying on the creating
 * function's stack frame or TypeScript's knowledge of the initializer.
 */
function escapedLocalCallback(flag: boolean): (unit: null) => boolean {
  const callback: ((unit: null) => boolean) | null = (unit: null): boolean =>
    flag;
  if (callback === null) {
    return (unit: null): boolean => false;
  }
  return (unit: null): boolean => callback(unit);
}

/**
 * The outer guard occurs after this closure is created. The closure therefore
 * checks its own nullable capture; a later guard at the call site cannot supply
 * a creation-time fact for the closure body.
 */
function laterGuardedCallback(flag: boolean): boolean {
  const callback: ((unit: null) => boolean) | null = (unit: null): boolean =>
    flag;
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    callback === null ? false : callback(unit);
  if (callback === null) {
    return false;
  }
  return invoke(null);
}

/**
 * Eliminating undefined leaves null as a separate possibility. The returned
 * closure keeps that partial refinement and must still guard null before call.
 */
function twoAbsenceCapture(flag: boolean): (unit: null) => boolean {
  const callback: ((unit: null) => boolean) | null | undefined = (
    unit: null,
  ): boolean => flag;
  if (callback === undefined) {
    return (unit: null): boolean => false;
  }
  return (unit: null): boolean => (callback === null ? false : callback(unit));
}

/**
 * The continuation of a returning disjunction excludes both absence tags.
 * Both facts must be available when the returned closure captures the callback.
 */
function compoundAbsenceCapture(flag: boolean): (unit: null) => boolean {
  const callback: ((unit: null) => boolean) | null | undefined = (
    unit: null,
  ): boolean => flag;
  if (callback === null || callback === undefined) {
    return (unit: null): boolean => false;
  }
  return (unit: null): boolean => callback(unit);
}

/**
 * The disjunction can succeed because of flag even when callback is null.
 * Its returned closure therefore needs its own null guard; a fact from only
 * the left successful path is not a fact about the entire branch.
 */
function ambiguousCaptureGuard(flag: boolean): (unit: null) => boolean {
  const callback: ((unit: null) => boolean) | null = (unit: null): boolean =>
    flag;
  if (callback !== null || flag) {
    return (unit: null): boolean =>
      callback === null ? false : callback(unit);
  }
  return (unit: null): boolean => false;
}

/**
 * A Boolean returned by a probing closure is not a type-predicate contract.
 * Even on its true branch, the caller must guard the nullable callback itself.
 */
function callbackProbeDoesNotNarrow(flag: boolean): boolean {
  const callback: ((unit: null) => boolean) | null = (unit: null): boolean =>
    flag;
  const present: (unit: null) => boolean = (unit: null): boolean =>
    callback !== null;
  if (present(null)) {
    return callback === null ? false : callback(null);
  }
  return false;
}

/**
 * Selection captures a callable value once. One alternative reads the shared
 * cell when called; the other retains the seed value. A later write changes
 * the live reader's observation without changing which callable was selected.
 */
function selectedCallableAfterMutation(seed: boolean): (unit: null) => boolean {
  const cell: { value: boolean } = { value: seed };
  const live: (unit: null) => boolean = (unit: null): boolean => cell.value;
  const snapshot: (unit: null) => boolean = (unit: null): boolean => seed;
  const selected: (unit: null) => boolean = seed ? live : snapshot;
  const invoke: (unit: null) => boolean = (unit: null): boolean =>
    selected(unit);
  cell.value = !seed;
  return invoke;
}

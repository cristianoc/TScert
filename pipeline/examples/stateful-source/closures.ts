/**
 * Capture a reference, then mutate it through an alias before calling the
 * closure. The call must read the current false value, not the value at
 * capture time.
 */
function capturedRead(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const read: (unit: null) => boolean = (unit: null): boolean => cell.value;
  const alias: { value: boolean } = cell;
  alias.value = false;
  return read(null);
}

/**
 * Capture an older immutable binding past an unrelated local. The closure must
 * retain the correct lexical value.
 */
function captureOlder(): true {
  const value: true = true;
  const other: false = false;
  const read: (unit: null) => true = (unit: null): true => value;
  return read(null);
}

/**
 * Return a closure that keeps its allocated cell reachable after the outer
 * function returns. Its contract remains valid for later calls.
 */
function escapingReader(seed: boolean): (unit: null) => boolean {
  const cell: { value: boolean } = { value: seed };
  return (unit: null): boolean => cell.value;
}

/**
 * Check a true-valued closure body against a Boolean result contract. Calling
 * the closure exposes that declared contract.
 */
function widenedBody(): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => true;
  return run(null);
}

/**
 * Use an assignment as a closure result. The closure mutates its captured cell
 * and returns the assigned false value.
 */
function writingBody(): boolean {
  const cell: { value: boolean } = { value: true };
  const run: (unit: null) => boolean = (unit: null): boolean =>
    (cell.value = false);
  return run(null);
}

/**
 * Allocate and immediately read a local cell inside a closure expression. This
 * exercises allocation beneath a function call.
 */
function allocatingBody(): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean =>
    ({ value: true }).value;
  return run(null);
}

/**
 * Call one closure from another after mutating their shared captured cell. The
 * nested call must observe the later write.
 */
function callingBody(): boolean {
  const cell: { value: boolean } = { value: true };
  const read: (unit: null) => boolean = (unit: null): boolean => cell.value;
  const run: (unit: null) => boolean = (unit: null): boolean => read(null);
  cell.value = false;
  return run(null);
}

/**
 * Read a captured cell from a block-bodied closure. Its return statement
 * environment is checked as well as its expression claim.
 */
function blockReader(): boolean {
  const cell: { value: boolean } = { value: true };
  const read: (unit: null) => boolean = (unit: null): boolean => {
    return cell.value;
  };
  cell.value = false;
  return read(null);
}

/**
 * Introduce closure-local bindings, write through a local cell, and return its
 * contents. Every statement claim must be justified in that local scope.
 */
function localBlock(): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    const saved: boolean = false;
    cell.value = saved;
    return cell.value;
  };
  return run(null);
}

/**
 * Use a captured Boolean test to prove that both closure arms return true. The
 * tested binding itself is true only in the first arm.
 */
function branchingClosure(flag: boolean): true {
  const run: (unit: null) => true = (unit: null): true => {
    if (flag) {
      return flag;
    } else {
      return true;
    }
  };
  return run(null);
}

/**
 * Refine captured and local Booleans in nested closure branches. Each return
 * is checked in the environment for its own path.
 */
function nestedBranches(flag: boolean, other: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const saved: boolean = other;
    if (flag) {
      if (saved) {
        return saved;
      } else {
        const result: boolean = false;
        return result;
      }
    } else {
      return flag;
    }
  };
  return run(null);
}

/**
 * Use a closure call as the condition after changing the captured cell. The
 * condition observes current state, and does not justify a persistent
 * refinement of the cell.
 */
function capturedBranch(): boolean {
  const cell: { value: boolean } = { value: true };
  const read: (unit: null) => boolean = (unit: null): boolean => cell.value;
  const run: (unit: null) => boolean = (unit: null): boolean => {
    if (read(null)) {
      return true;
    } else {
      return false;
    }
  };
  cell.value = false;
  return run(null);
}

/**
 * Write a closure-local cell in both arms, then share one return. Arm-local
 * bindings disappear at the join.
 */
function joinedClosure(flag: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    if (flag) {
      const saved: boolean = flag;
      cell.value = saved;
    } else {
      cell.value = false;
    }
    return cell.value;
  };
  return run(null);
}

/**
 * Let nested branches fall through into a shared read. The cell invariant must
 * justify the continuation regardless of which writes occurred.
 */
function nestedFallThrough(flag: boolean, other: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    if (flag) {
      if (other) {
        cell.value = false;
      }
    }
    const saved: boolean = cell.value;
    return saved;
  };
  return run(null);
}

/**
 * Return early from a closure when flag is true. The remaining path may use
 * the fact that the same immutable flag is false.
 */
function earlyReturn(flag: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    if (flag) {
      return flag;
    }
    return flag;
  };
  return run(null);
}

/**
 * Return from the else arm and continue after the writing arm. Its local saved
 * binding must be dropped before the later binding with the same name.
 */
function earlyReturnElse(flag: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    const cell: { value: boolean } = { value: true };
    if (flag) {
      const saved: boolean = false;
      cell.value = saved;
    } else {
      return flag;
    }
    const saved: boolean = cell.value;
    return saved;
  };
  return run(null);
}

/**
 * Chain two early returns inside a closure. Each surviving path carries the
 * refinements established by the preceding tests.
 */
function successiveReturns(flag: boolean, other: boolean): boolean {
  const run: (unit: null) => boolean = (unit: null): boolean => {
    if (flag) {
      return flag;
    }
    if (other) {
      return other;
    }
    return other;
  };
  return run(null);
}

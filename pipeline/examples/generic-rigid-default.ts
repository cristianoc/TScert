// The default is universally valid, but its input contract needs T | undefined
// in the rigid claim/certificate language; replacing T with its bound is wrong.
function rigidDefault(seed: boolean): boolean {
  const pick = <T>(value: T, copy: T = value): T => copy;
  return pick(seed);
}

// T may itself contain undefined. Initialization must not narrow T by deleting
// undefined from the instantiated input type.
function undefinedRigidDefault(seed: boolean | undefined): boolean | undefined {
  const pick = <T>(value: T, copy: T = value): T => copy;
  return pick(seed);
}

// Forward capture and a rigid default share the same initialization schedule.
function genericDeferredDefault(seed: boolean): boolean {
  const pick = <T>(
    value: T,
    read: () => T = (): T => later,
    later: T = value,
  ): T => read();
  return pick(seed);
}

// One observed boolean instantiation cannot justify a boolean default for T.
function specializedRigidDefault(seed: boolean): boolean {
  const pick = <T>(value: T, copy: T = true): T => copy;
  return pick(seed);
}

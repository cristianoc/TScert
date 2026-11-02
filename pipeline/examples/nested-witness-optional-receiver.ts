// Census functions:
// fragment-classes.mts#ownClass
class Gate {
  selfClass: { name: string; generic: boolean } | null = null;
  classReads: Map<string, string> = new Map();
  fail(message: string): void {
    throw Error(message);
  }
}
export function own(this: Gate, key: string): string | null {
  const gate: Gate = this;
  const cls = gate.classReads.get(key);
  if (!cls || cls !== gate.selfClass?.name) return null;
  if (gate.selfClass.generic) gate.fail("generic");
  return cls;
}

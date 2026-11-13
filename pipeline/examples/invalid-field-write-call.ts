// A call between a field's write and its read: the callee may write the
// field again, so the read is of the field's declared type. TypeScript keeps
// the narrowing. Under Node the callback clears the field and `null` is
// returned where the slots are.
// On the single pass, a gap: the single pass refuses the field's `??=` write
// before the read after the call.
type Slots = { observation: string; result: string | null };
type Binder = { name: string; resolution: Slots | null };

export function cached(binder: Binder, log: () => void): Slots {
  binder.resolution ??= { observation: binder.name, result: null };
  log();
  return binder.resolution;
}

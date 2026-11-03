// A field of an immutable binding's object holds what was last written to
// it until a call or another write: `x.f = v` and `x.f ??= v` leave the
// field at the written value's nullish exclusions, and a strict test of a
// path of two members refines its witness (HOST-FAMILIES.md, "Entries"), as
// type-term.mts's `quantified` caches a binder's resolution slots and reads
// their result.
type Slots = { observation: string; result: string | null };
type Binder = { name: string; resolution: Slots | null };

function slots(name: string, resolvable: boolean): Slots {
  return {
    observation: `#observe:${name}`,
    result: resolvable ? `#resolve:${name}` : null,
  };
}

// The cached slots' result, where the binder's resolution is resolvable.
export function resolved(binder: Binder, resolvable: boolean): string | null {
  binder.resolution ??= slots(binder.name, resolvable);
  if (binder.resolution.result === null) return null;
  return binder.resolution.result;
}

// A plain write, then a read of the field it wrote.
export function written(binder: Binder): Slots {
  binder.resolution = slots(binder.name, false);
  return binder.resolution;
}

// A path of two members tested against `null` in one statement and read in
// the next.
export function result(binder: { readonly resolution: Slots }): string {
  if (binder.resolution.result === null) return "";
  return binder.resolution.result;
}

// A method of a scope whose type states its effect, writing a field of a
// binder it finds, an intersection whose principal operand states the field:
// a named field's write changes a value's location, within the statement's
// footprint, as `quantified`'s `associated` does.
type Scope = {
  associated: (
    name: string,
  ) => Within<{ value: "any"; store: "keep" }, string | null>;
};

export function scope(binders: (Binder & { span: number })[]): Scope {
  return {
    associated(name) {
      const binder = binders.find((b) => b.name === name);
      if (!binder) return null;
      binder.resolution ??= slots(binder.name, true);
      return binder.resolution.result;
    },
  };
}

// Types declared in a body closing over the enclosing function's type
// parameters: each is lifted over them, its own parameters after.

// An interface declared twice in one block is one interface closing over
// `T` and binding its own `U`, each part's members read with both.
function merged<T>(value: T): T {
  interface Slot<U> {
    value: T;
  }
  interface Slot<U> {
    extra: U[];
  }
  const slot: Slot<string> = { value, extra: ["x"] };
  return slot.value;
}

// An own parameter shadows the captured one of its spelling; a default reads
// the captured one.
function shadowedParameter<T>(value: T, label: string): string {
  type Same<T> = { own: T };
  type Defaulted<U = T[]> = { items: U };
  const same: Same<string> = { own: label };
  const defaulted: Defaulted = { items: [value] };
  return same.own + defaulted.items.length;
}

// A block's type hides the enclosing type parameter of its spelling: in the
// block `T` is `string`, and nothing there closes over the parameter.
function hiddenParameter<T>(value: T): string {
  {
    type T = string;
    type Labels = T[];
    const labels: Labels = ["x"];
    const label: T = labels.length ? "y" : "z";
    return label + String(value === value);
  }
}

// A generic closure sees the alias at the outer binder, which no nearer
// binder hides; a local alias naming another captures it too.
function nested<T>(value: T): T[] {
  type Many = T[];
  type Pair = { first: Many; second: Many };
  const twice = <U>(extra: U): Pair => {
    const many: Many = [value];
    return { first: many, second: extra === extra ? many : [] };
  };
  return twice(0).first;
}

// A block type naming no binder closes over none: the rest pack `T` is no
// argument of it.
function packed<T extends unknown[]>(...args: T): number {
  type Count = number;
  const count: Count = args.length;
  return count;
}

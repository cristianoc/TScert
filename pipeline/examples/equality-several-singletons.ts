// A comparison with a union of singletons is tested one singleton at a time:
// where equal, both operands narrow, fields included.

type Wide = { field: 0 | 1 | 2 } | { field: 3 };

// A field against a name holding one of several singletons: the field, and
// the object's arms.
function fieldAgainstName(obj: Wide, x: 0 | 1): 0 | 1 {
  if (obj.field === x) {
    const f: 0 | 1 = obj.field;
    const narrowed: { field: 0 | 1 | 2 } = obj;
    return f;
  }
  return 0;
}

// Two fields: each narrows to what the other may hold.
function fieldAgainstField(o1: { a: 0 | 1 | 2 }, o2: { b: 1 | 2 | 3 }): 1 | 2 {
  if (o1.a === o2.b) {
    const a: 1 | 2 = o1.a;
    const b: 1 | 2 = o2.b;
    return b;
  }
  return 1;
}

declare function oneOrTwo(): 1 | 2;

// A call is evaluated once, then split; the name narrows.
function nameAgainstCall(x: 0 | 1 | 2): 1 | 2 {
  if (x === oneOrTwo()) {
    return x;
  }
  return 1;
}

// A family found equal to one of its values is that value.
function familyToSingleton(x: number, o: { s: string }): 1 {
  if (o.s === "a") {
    const a: "a" = o.s;
  }
  if (x === 1) {
    return x;
  }
  return 1;
}

// Of a union of records each naming the field, the field is known too.
function unionField(
  x: { f: number | null } | { f: number; g: string },
): number {
  if (x.f !== null) {
    return x.f;
  }
  return 0;
}

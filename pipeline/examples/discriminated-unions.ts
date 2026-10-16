// A test of a field against a singleton keeps the arms of the object's union
// whose field admits the outcome. An object's arm is fixed where it is
// allocated, so the narrowing survives writes and calls; what the field holds
// is known only until a step may write it.
type Shape =
  | { kind: "circle"; radius: number }
  | { kind: "square"; side: number }
  | { kind: "rect"; w: number; h: number };

function area(s: Shape): number {
  if (s.kind === "circle") {
    return s.radius * s.radius;
  }
  if (s.kind !== "square") {
    return s.w * s.h;
  }
  return s.side * s.side;
}

function measure(s: Shape): number {
  switch (s.kind) {
    case "circle":
      return s.radius;
    case "square":
      return s.side;
    case "rect":
      return s.w;
  }
}

type Box = { tag: 0; value: number } | { tag: 1; value: string };

function afterWrite(b: Box, c: { n: number }): number {
  if (b.tag === 0) {
    c.n = 1;
    return b.value;
  }
  return 0;
}

function fieldGuard(o: { val: string | null }): string {
  if (o.val !== null) {
    return o.val;
  }
  return "";
}

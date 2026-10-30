// A `switch (typeof x)` tests the shape of `x`: each test is the `typeof`
// test of `x` read again, so a clause sees `x` narrowed to the shape its
// label names, `default` the rest, for a name and a field of a name. Two
// labels sharing a clause see either shape.
// Model study: proposal-boolean-member-read.ts.
export function describe(v: string | number | boolean): string {
  switch (typeof v) {
    case "string":
      return v;
    case "number":
      return v.toFixed(2);
    case "boolean":
      return v ? "yes" : "no";
  }
}

export function field(o: { readonly f: string | number | undefined }): number {
  switch (typeof o.f) {
    case "number":
      return o.f;
    case "string":
      return o.f.length;
    default:
      return 0;
  }
}

export function shared(v: string | number | (() => number)): string {
  switch (typeof v) {
    case "string":
    case "number":
      return String(v);
    default: {
      const n: number = v();
      return n.toFixed(0);
    }
  }
}

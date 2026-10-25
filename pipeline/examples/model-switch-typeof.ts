// A switch on typeof needs to narrow the original value in each arm.
// Model study: proposal-boolean-member-read.ts; study count not supplied.
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

// Where `x instanceof IoFailure` fails, `x` may still be an `IoFailure`: the
// class type is structural, and a record with its members meets it without
// its prototype. TypeScript narrows the failed arm to `string` and would
// return the record as a string (run under Node).
import { IoFailure } from "@fixture/failures";

export function label(x: IoFailure | string): string {
  if (x instanceof IoFailure) {
    return "failure";
  }
  return x;
}

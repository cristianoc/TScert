// At a position of a host declaration an enum type is `number`: TypeScript
// admits any number there, and the flag enums hold combinations of members.
// A `switch` with a case per member and no default may complete without a
// return, so the function is refused at its end.
import { DiagnosticCategory, type Diagnostic } from "typescript/unstable/sync";

export function severity(d: Diagnostic): string {
  switch (d.category) {
    case DiagnosticCategory.Warning:
      return "warning";
    case DiagnosticCategory.Error:
      return "error";
    case DiagnosticCategory.Suggestion:
      return "suggestion";
    case DiagnosticCategory.Message:
      return "message";
  }
}

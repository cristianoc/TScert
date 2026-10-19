// The message is read-only through every alias: a write through a parameter
// is refused.
class Decline extends Error {}
export function relabel(e: Decline): void {
  e.message = "relabelled";
}

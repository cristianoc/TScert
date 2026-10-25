// A unit's own promise remains an aggregate obligation.
export function predicate(value: unknown): value is string {
  return true;
}

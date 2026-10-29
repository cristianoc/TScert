// Omit keeps a kept member's readonly modifier: a write through an assertion
// to a writable record is refused.
interface Entry {
  stated: number;
  readonly name: string;
}
export function write(e: Omit<Entry, "stated">): void {
  (e as { name: string }).name = "m";
}

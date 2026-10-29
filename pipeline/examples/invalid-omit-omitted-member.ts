// Omit removes the omitted member: a value at `Omit<Entry, "stated">` need
// not hold `stated`, so a read of it through an assertion to `Entry` is not
// a number.
interface Entry {
  stated: number;
  name: string;
}
export function stated(e: Omit<Entry, "stated">): number {
  return (e as Entry).stated;
}
export const run = (): number => stated({ name: "n" });

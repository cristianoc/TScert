// Contextual construction retains every index of an intersected union.
type Result<T> = ({ unobserved: string } | { identity: string }) & {
  readonly [field: string]: string;
} & {
  readonly [field: string]: T;
};
export function wrong(): Result<boolean> {
  return { unobserved: "missing compiler" };
}

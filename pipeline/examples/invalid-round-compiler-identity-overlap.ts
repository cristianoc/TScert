// Every overlapping field constraint remains an introduction obligation.
type Result = ({ unobserved: string } | { identity: string }) & {
  unobserved: boolean;
};
export function wrong(): Result {
  return { unobserved: "missing compiler" };
}

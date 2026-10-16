// A parameter written as a pattern or with a default binds a hidden name;
// the body's first statements bind the source's names from it, in order.
type Numbers = number[];

function objectParameter({ x, y }: { x: number; y: string }): string {
  return y;
}
function nestedParameter({
  point: [x, y],
}: {
  point: [number, number];
}): number {
  return x + y;
}
function defaultParameter(x: number = 0): number {
  return x;
}
function dependentDefault(first: number, second: number = first): number {
  return second;
}
function patternDefault(
  { value }: { value: string } | undefined = { value: "ready" },
): string {
  return value;
}
function callsDefault(): number {
  return defaultParameter() + defaultParameter(1);
}
// A closure's parameter pattern, and a pattern in a closure body.
function arrowPatterns(): number {
  const first = ([a, b]: [number, string]): number => a;
  const second = ({ x = 0 }: { x?: number }): number => {
    const { y } = { y: x };
    return y;
  };
  return first([1, "b"]) + second({});
}
// A rest parameter collects a fresh array, which may be viewed readonly or
// named through an alias.
function readonlyRest(...x: readonly number[]): ReadonlyArray<number> {
  return x;
}
function aliasRest(...nums: Numbers): number {
  nums.push(1);
  return nums.length;
}

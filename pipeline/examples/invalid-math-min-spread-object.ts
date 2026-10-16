// A spread passes each element as an argument: `Math.min(...os)` converts
// every object by its own `valueOf`, which here writes `seen.value`.
export function wrong(os: { valueOf(): number }[], seen: { value: 0 }): 0 {
  // @ts-expect-error TypeScript refuses the objects too
  Math.min(...os);
  return seen.value;
}

// The incoming edge belongs to a closure, whose enclosing expression is opaque.
export function closureEdge(value: unknown): () => string {
  return (): string => {
    let result: string = "";
    result = value;
    return result;
  };
}

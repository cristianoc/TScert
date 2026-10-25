// Local inspection admits closure code; aggregate checking must inspect its body.
export function closure(value: number): () => string {
  return () => value as string;
}

export function sibling(value: boolean): number {
  return value as number;
}

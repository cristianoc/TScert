interface Entry { stated: number; name: string }
export function g<T extends Entry>(e: Omit<T, "stated">): string {
  return "x";
}

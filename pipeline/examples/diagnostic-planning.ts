// A planning refusal must leave later independent expression obligations visible.
export function named(value: object, flag: boolean): number {
  if ("name" in value) {
    return flag as number;
  }
  return 0;
}

export function sibling(value: number): string {
  return value as string;
}

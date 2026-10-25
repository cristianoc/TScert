import { sep } from "node:path";

export function imported(value: number): string {
  const marker = sep;
  return value as string;
}

export function independent(flag: boolean): number {
  return flag as number;
}

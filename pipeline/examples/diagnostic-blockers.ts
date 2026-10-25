export function first(x: number): string {
  const y: string = x as string;
  return y;
}

export function second(x: boolean): number {
  return x as number;
}

export function branch(flag: boolean, value: number): string {
  let result: string = "";
  if (flag) {
    const chosen = value as string;
    result = chosen;
  } else {
    result = "other";
  }
  return result;
}

export function handled(value: number): string {
  try {
    return value as string;
  } catch (error) {
    return "caught";
  }
}

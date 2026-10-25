// The assignment leaves a local slot outside the following point's contract.
export function edge(value: unknown): string {
  let result: string = "";
  result = value;
  return result;
}

export function branches(flag: boolean, value: unknown): string {
  let result: string = "";
  if (flag) result = value;
  else result = "other";
  return result;
}

export function handled(value: unknown): string {
  let result: string = "";
  try {
    result = value;
    throw "stop";
  } catch {
    return result;
  }
}

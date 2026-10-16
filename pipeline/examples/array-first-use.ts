// An unannotated constant's fresh array is built at the array type its first
// use expects: an annotated constant, a call's parameter, a return.
type Mixed = string | number | { x: number };
declare function takesLiteralTuple(values: [1, 2]): void;

export function tuple(): number {
  const values = [1, 2];
  const pair: [number, number] = values;
  return pair[0];
}

export function literal(): void {
  const values = [1, 2];
  takesLiteralTuple(values);
  takesLiteralTuple(values);
}

export function wider(): Mixed[] {
  const arr = ["a", 1];
  const view: Mixed[] = arr;
  arr[0] = { x: 42 };
  return view;
}

export function returned(): [string, number] {
  const values = ["a", 1];
  return values;
}

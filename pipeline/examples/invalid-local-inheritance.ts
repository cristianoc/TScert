interface Base {
  readonly flag: boolean;
}

interface Derived extends Base {
  readonly label: string;
}

export function wrong(value: Derived): number {
  return value.flag;
}

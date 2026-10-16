interface Base {
  readonly flag: boolean;
}

interface Derived extends Base {
  readonly label: string;
}

export function inherited(value: Derived): boolean {
  return value.flag;
}

export function owned(value: Derived): string {
  return value.label;
}

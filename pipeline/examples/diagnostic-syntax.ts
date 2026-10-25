export function syntax(x: number): string {
  debugger;
  debugger;
  return x as string;
}

class Prepared {
  value: number = 0;
  constructor() {
    this.value = this.value + 1;
  }
}

export function hoisted(x: boolean): number {
  return x as number;
  function dead(): number {
    return 0;
  }
}

// A block-bodied closure that does not return on every path falls off its
// end, which returns undefined: annotated `void` or `T | undefined`, or left
// to the producer.
function voidCallback(seed: boolean): void {
  const discard = (x: boolean): void => {};
  discard(seed);
}

function setLater(flag: boolean): boolean {
  let x: boolean = false;
  const set = (): void => {
    x = flag;
  };
  set();
  return x;
}

function maybe(flag: boolean): number | undefined {
  const f = (): number | undefined => {
    if (flag) {
      return 1;
    }
  };
  return f();
}

function unannotated(flag: boolean): undefined {
  const f = () => {
    const g = flag;
  };
  return f();
}

function early(flag: boolean): number | undefined {
  const f = (): number | undefined => {
    if (flag) return;
    return 2;
  };
  return f();
}

async function settle(flag: boolean): Promise<void> {
  if (flag) return;
}

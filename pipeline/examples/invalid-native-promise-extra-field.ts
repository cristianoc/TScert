interface Promise<T> {
  n: number;
}

async function made(): Promise<number> {
  return 1;
}

function ownValue(): number {
  const p = made();
  return p.n;
}

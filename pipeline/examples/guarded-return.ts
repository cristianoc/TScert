// `if (x.f !== c) return x.f;`: the tested read is what the arm returns, in a
// function body and in a closure, through a `let` the closure captures.
export function direct(seed: boolean | null): boolean {
  let cell = { value: seed };
  cell = { value: null };
  if (cell.value !== null) return cell.value;
  return false;
}

export function captured(seed: boolean | null): boolean {
  let cell = { value: seed };
  const read = (): boolean => {
    if (cell.value !== null) return cell.value;
    return false;
  };
  cell = { value: null };
  return read();
}

declare function callbackResult(cell: { value: number }): {
  readonly tag: number;
};

async function forward(
  p: Promise<number>,
  cell: { value: number },
): Promise<number> {
  await p.finally(() => callbackResult(cell));
  return cell.value;
}

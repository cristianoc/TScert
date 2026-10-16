export function caught(p: Promise<number>): Promise<number> {
  return p.catch();
}

export function finalized(p: Promise<number>): Promise<number> {
  return p.finally();
}

export function mapped(p: Promise<{ n: number }>): Promise<number> {
  return p.then((record: { n: number }): number => record.n);
}

export function finalizedPromise(
  p: Promise<number>,
  cleanup: Promise<{ n: number }>,
): Promise<number> {
  return p.finally((): Promise<{ n: number }> => cleanup);
}

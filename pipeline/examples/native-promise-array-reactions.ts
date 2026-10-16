export function caught(p: Promise<number[]>): Promise<number[]> {
  return p.catch();
}

export function finalized(p: Promise<number[]>): Promise<number[]> {
  return p.finally();
}

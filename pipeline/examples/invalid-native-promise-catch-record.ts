export function forward(p: Promise<{ n: number }>): Promise<{ n: number }> {
  return p.catch();
}

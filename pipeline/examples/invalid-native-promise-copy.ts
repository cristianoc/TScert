export function fake(p: Promise<number>): Promise<number> {
  return { ...p };
}

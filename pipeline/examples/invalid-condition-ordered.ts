// The right operand of `(first === undefined || …) && …` runs where
// `first` is undefined: its cast there is refused (`wrong([], undefined)`
// throws under Node).
function step(log: string[], name: string): boolean {
  log.push(name);
  return name.length > 1;
}
export function wrong(log: string[], first: string | undefined): string[] {
  if (
    (first === undefined || step(log, first)) &&
    (log.push("c"), (first as string).length > 0)
  )
    log.push("e");
  return log;
}

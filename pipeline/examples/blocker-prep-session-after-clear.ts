// Census functions:
// declaration-session.mts#inDeclarationAttempt
// declaration-session.mts#settleDeclarationSession
type Session = { ledger: object; name: string };
let retained: Session | null = null;
function close(s: Session): void {
  s.name = "";
}
export function settle(ledger: object): void {
  const s = retained;
  if (s?.ledger === ledger) {
    retained = null;
    close(s);
  }
}

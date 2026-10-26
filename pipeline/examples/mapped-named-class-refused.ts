// A mapped type at a class: a class's instance type holds its private
// members, which TypeScript's `keyof` does not list, and the reader refuses
// it.
class Account {
  private secret: number = 0;
  balance: number = 0;
}
export function balance(a: Partial<Account>): number {
  return a.balance ?? 0;
}

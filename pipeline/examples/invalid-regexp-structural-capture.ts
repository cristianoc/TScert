// A `RegExp` parameter may be any value meeting the structural contract:
// every capture may be unmatched.
export function key(re: RegExp, s: string): string {
  const m = re.exec(s);
  return m ? m[1] : "";
}

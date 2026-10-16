// A function is no Json value: the literal built at the bound's dictionary
// arm does not meet it.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
function keep<T extends Json>(x: T): T {
  return x;
}
export function bad(): Json {
  return keep({ name: "test", f: () => 1 });
}

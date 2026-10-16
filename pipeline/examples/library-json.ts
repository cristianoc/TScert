// `JSON.parse` is a value of which nothing is known, or a SyntaxError;
// `JSON.stringify` of a `JsonValue`, a primitive or a dictionary of them,
// is a string: such a value owns nothing the host would call, `toJSON`
// included.
function decode(text: string): unknown {
  return JSON.parse(text);
}

function encode(n: number, s: string | null, flag: boolean): string {
  return JSON.stringify(n) + JSON.stringify(s) + JSON.stringify(flag);
}

function record(): string {
  return JSON.stringify({ a: 1, b: { c: "x", d: null } });
}

function dictionary(d: { readonly [k: string]: number }): string {
  return JSON.stringify(d);
}

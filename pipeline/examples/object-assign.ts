// `Object.assign` copies each source onto its target, as a spread copies,
// where nothing else can see the target change: onto a fresh literal, whose
// result is the call's value, or, as a statement, onto a local's own object,
// which the local holds from then on.
export function fresh(): { a: number; b: string } {
  return Object.assign({ a: 1 }, { b: "s" });
}

export function owned(): { a: number; b: string; c: boolean } {
  const o = { a: 1 };
  Object.assign(o, { b: "s" }, { c: true });
  return o;
}

// A source a spread built owns only the keys it copied.
export function spreadSource(p: { b: string }): { a: number; b: string } {
  return Object.assign({ a: 1 }, { ...{ b: p.b } });
}

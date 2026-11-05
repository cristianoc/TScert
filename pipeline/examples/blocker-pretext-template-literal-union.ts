// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit,
// with the rewrites of issue #94): line-breaks.ts#getBlinkLineBreaks.
// Refusal: reject: source expression obligation: no derivation of its
// node-typing claim.
// A template literal whose hole holds a union of string literals, passed
// where a union of literals is expected: TypeScript types it as the union
// of its instances, `"chromium/line_normal" | "chromium/line_normal_cj"`;
// the model types a concatenation as `string`, as it does `'a' + b` of
// literals.
type RuleTable =
  | "apple/line"
  | "chromium/line_normal"
  | "chromium/line_normal_cj";

function rules(table: RuleTable): number {
  return table.length;
}

export function blinkRules(cj: boolean): number {
  const table: "line_normal" | "line_normal_cj" = cj
    ? "line_normal_cj"
    : "line_normal";
  return rules(`chromium/${table}`);
}

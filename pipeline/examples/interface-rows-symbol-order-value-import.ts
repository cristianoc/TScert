// An importer whose document lists its unique symbols in another order than
// the module it reads (pretext's prepare.ts, analysis.ts, measurement.ts and
// han-kerning.ts reading checked.ts's `missing` and line-breaks.ts's
// `hasProperty`: `getScriptFacts`, `needsComplexTextPath`,
// `mapSourceLineBreaks`, `getFontData`, `getWebKitGenericFamilies`): its
// regular expression lists the regular-expression symbols before `Map`'s,
// so the module's interface rows and the importer's store name
// `Symbol.toStringTag` by different indices. Each reads every symbol key at
// its declaration's canonical number, so the rows agree, `count` is read at
// its certified footprint, which writes nothing, and `xs[i]!` keeps its bound
// across the call.
import { count } from "@fixture/symbol-order";

const pattern = /a/;

export function matches(s: string): boolean {
  return pattern.test(s);
}

export function widest(xs: number[], m: Map<string, number>): number {
  let widest = 0;
  for (let i = 0; i < xs.length; i++) {
    const limit = count(m, "k");
    if (xs[i]! <= limit && xs[i]! > widest) widest = xs[i]!;
  }
  return widest;
}

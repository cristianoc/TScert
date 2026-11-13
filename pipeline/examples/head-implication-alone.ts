// Implications the front proposes at a loop head before two branches on
// `preserve` (`preserve ? 1 : 2`, `keepAll && !preserve`): the head's
// implication of `wordBreak` no edge establishes is left out alone, and
// `preserve → whiteSpace: "pre-wrap"` stays for the true arm of `preserve ?
// … : …` after the loop (pretext's `analyzeText`).
export function choose(whiteSpace: "normal" | "pre-wrap", wordBreak: "normal" | "keep-all", n: number): number {
  const preserve = whiteSpace === "pre-wrap";
  let t = 0;
  for (let k = 0; k < n; k++) t += 1;
  const chosen = preserve ? 1 : 2;
  const keepAll = wordBreak === "keep-all";
  if (keepAll && !preserve) t = chosen;
  return t;
}

export function assign(text: string, whiteSpace: "normal" | "pre-wrap", wordBreak: "normal" | "keep-all", n: number): number {
  const preserve = whiteSpace === "pre-wrap";
  let t = 0;
  for (let k = 0; k < n; k++) t += 1;
  let normalized: string;
  if (preserve) normalized = text + "a";
  else normalized = text + "b";
  const keepAll = wordBreak === "keep-all";
  if (keepAll && !preserve) t = normalized.length;
  return t;
}

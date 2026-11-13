// A branch on a Boolean binding in a loop (`eastAsian && …`, `eastAsian`
// true giving `scan: "gecko"`), a nested loop after it in the same loop:
// the implication the branch reads is proposed at the nested loop's head
// too, which the outer loop's back edge crosses before reaching the branch
// again (pretext's `removeSkippableSegmentBreaks`, its helpers stubbed).
const maybeEastAsianRe = /[\u1100-\uFFFF]/;
function isJapaneseOrChinese(language: string | null): boolean {
  return language === "ja";
}
function isSegmentBreakRunSpace(
  code: number,
  scan: "blink" | "gecko",
): boolean {
  return code === 32 || (scan === "gecko" && code === 9);
}
function isDiscardable(code: number, b: boolean): boolean {
  return code === 0xad || b;
}
function isSpaceCombiningSequenceTail(text: string, end: number): boolean {
  return end < text.length;
}
function isEastAsianSegmentBreak(
  text: string,
  start: number,
  end: number,
  japaneseOrChinese: boolean,
): boolean {
  return start > 0 && end < text.length && japaneseOrChinese;
}
export type AnalysisProfile = {
  lineBreakScan: "blink" | "webkit" | "gecko";
  hangTabs: boolean;
};

export function full(
  text: string,
  profile: AnalysisProfile,
  language: string | null = null,
): string {
  const scan = profile.lineBreakScan;
  if (scan === "webkit" || !text.includes("\n")) return text;
  const eastAsian = scan === "gecko" && maybeEastAsianRe.test(text);
  if (!eastAsian && !text.includes("\u200B")) return text;
  const japaneseOrChinese = eastAsian && isJapaneseOrChinese(language);
  let result = "";
  let copied = 0;
  for (let newline = text.indexOf("\n"); newline !== -1; ) {
    let start = newline;
    for (let index = newline - 1; index >= 0; index--) {
      const code = text.charCodeAt(index);
      if (isSegmentBreakRunSpace(code, scan)) start = index;
      else if (!(scan === "gecko" && isDiscardable(code, false))) break;
    }
    let end = newline + 1;
    let index = end;
    for (; index < text.length; index++) {
      const code = text.charCodeAt(index);
      if (isSegmentBreakRunSpace(code, scan)) end = index + 1;
      else if (!(scan === "gecko" && isDiscardable(code, false))) break;
    }
    newline = text.indexOf("\n", index);
    if (
      scan === "gecko" &&
      text.charCodeAt(end - 1) === 0x20 &&
      isSpaceCombiningSequenceTail(text, end)
    )
      end--;
    if (
      text.charCodeAt(start - 1) !== 0x200b &&
      text.charCodeAt(end) !== 0x200b &&
      !(
        eastAsian &&
        isEastAsianSegmentBreak(text, start, end, japaneseOrChinese)
      )
    )
      continue;
    result += text.slice(copied, start);
    for (let member = start; member < end; member++) {
      if (!isSegmentBreakRunSpace(text.charCodeAt(member), scan))
        result += text[member];
    }
    copied = end;
  }
  return copied === 0 ? text : result + text.slice(copied);
}

/** The capture shape of a regular expression literal (SOURCE-CONTRACTS.md,
 * "Regular expressions"): its number of capture groups, which of them take
 * part in every successful match, whether it has named groups, and whether
 * it is global. A trusted reading of ECMA-262's pattern grammar ("Patterns",
 * with Annex B's extensions outside Unicode mode), deliberately partial: a
 * form it does not read gives the conservative shape, never a refusal.
 *
 * A group takes part in every successful match when no ancestor of it in the
 * pattern's tree is a disjunction of two or more alternatives, a quantifier
 * with minimum 0, or a lookaround. A quantifier with minimum at least 1 keeps
 * its atom's groups: on success the last iteration matched the whole atom,
 * and `RepeatMatcher` rejects an empty iteration beyond the minimum.
 *
 * Escapes are read by mode. In Unicode mode (`u`, `v`), `\p{…}`, `\P{…}`,
 * `\u{…}` and `\k<…>` are single escapes. Outside it, `\p` and `\P` are the
 * letters, `\u` is `\uXXXX` with four hex digits or else the letter `u`, so
 * that `\u{a|x}` is `u{a`, an alternative, and `x}`; `\k<name>` is a back
 * reference only in a pattern with a named group, and else the letter `k`;
 * `\c` not followed by a letter is a literal backslash. The count and the
 * names are also checked against the host's own compilation of the pattern;
 * which groups take part is this reading's alone. */

export type RegExpShape = {
  /** For each capture group, in order: whether it holds a string in every
   * successful match. */
  always: boolean[];
  /** Whether the pattern names a group: a match's `groups` is then an object,
   * else `undefined`. */
  named: boolean;
  /** Whether the flags hold `g`. */
  global: boolean;
};

type Group = { always: boolean; name: string | null };

class Decline extends Error {}

/** A group name's code points: `\uXXXX` (a surrogate pair of two such
 * escapes included) and `\u{X…}` decoded, as the host keys `groups`. */
function decodeName(raw: string): string {
  const decoded = raw.replace(/\\u\{([0-9A-Fa-f]+)\}|\\u([0-9A-Fa-f]{4})/g,
    (_, point: string | undefined, unit: string | undefined) =>
      point !== undefined ? String.fromCodePoint(parseInt(point, 16)) : String.fromCharCode(parseInt(unit ?? "", 16)));
  if (decoded.includes("\\")) throw new Decline("an escape in a group name");
  return decoded;
}

/** The groups of `pattern` under `flags`, or a `Decline` thrown for a form
 * the reading leaves out. */
function groupsOf(pattern: string, flags: string): Group[] {
  if (flags.includes("v")) throw new Decline("class-set syntax (`v`)");
  const unicode = flags.includes("u");
  // A named group anywhere makes `\k<…>` a back reference outside Unicode
  // mode too.
  const namedContext = unicode || /\(\?<(?![=!])/.test(pattern.replace(/\\[\s\S]|\[(?:\\[\s\S]|[^\]\\])*\]/g, ""));
  const groups: Group[] = [];
  let i = 0;
  const at = (k: number): string => pattern[k] ?? "";
  const maybeFrom = (first: number): void => {
    for (let k = first; k < groups.length; k++) {
      const g = groups[k];
      if (g) g.always = false;
    }
  };
  const until = (close: string): void => {
    const end = pattern.indexOf(close, i);
    if (end < 0) throw new Decline(`an unterminated escape`);
    i = end + 1;
  };
  // An escape at `i` (a backslash): its end.
  const escape = (inClass: boolean): void => {
    const d = at(i + 1);
    if (d === "") throw new Decline("a trailing backslash");
    if ((d === "p" || d === "P") && unicode) { i += 2; if (at(i) !== "{") throw new Decline("`\\p` without braces"); until("}"); return; }
    if (d === "u") {
      if (unicode && at(i + 2) === "{") { i += 2; until("}"); return; }
      if (/^[0-9A-Fa-f]{4}$/.test(pattern.slice(i + 2, i + 6))) { i += 6; return; }
      if (unicode) throw new Decline("a malformed `\\u` escape");
      i += 2;
      return;
    }
    if (d === "k" && !inClass && namedContext) {
      if (at(i + 2) !== "<") throw new Decline("`\\k` without a name");
      i += 2;
      until(">");
      return;
    }
    if (d === "c" && !/[A-Za-z]/.test(at(i + 2))) {
      if (unicode) throw new Decline("a malformed `\\c` escape");
      i += 1;
      return;
    }
    if (d === "c") { i += 3; return; }
    i += 2;
  };
  const disjunction = (optional: boolean): void => {
    const first = groups.length;
    alternative(optional);
    let alternatives = 1;
    while (at(i) === "|") { i++; alternative(true); alternatives++; }
    if (alternatives > 1) maybeFrom(first);
  };
  const alternative = (optional: boolean): void => {
    while (i < pattern.length && at(i) !== "|" && at(i) !== ")") term(optional);
  };
  const term = (optional: boolean): void => {
    const first = groups.length;
    const c = at(i);
    if (c === "^" || c === "$") { i++; return; }
    if (c === "\\" && (at(i + 1) === "b" || at(i + 1) === "B")) { i += 2; return; }
    if (c === "\\") escape(false);
    else if (c === "[") {
      // ClassContents: `[]` and `[^]` are complete classes; the first
      // unescaped `]` closes the class.
      i++;
      if (at(i) === "^") i++;
      while (i < pattern.length && at(i) !== "]") {
        if (at(i) === "\\") escape(true);
        else i++;
      }
      if (at(i) !== "]") throw new Decline("an unterminated class");
      i++;
    } else if (c === "(") {
      i++;
      let capture = true, lookaround = false, name: string | null = null;
      if (at(i) === "?") {
        const k = at(i + 1);
        if (k === ":") { capture = false; i += 2; }
        else if (k === "=" || k === "!") { capture = false; lookaround = true; i += 2; }
        else if (k === "<" && (at(i + 2) === "=" || at(i + 2) === "!")) { capture = false; lookaround = true; i += 3; }
        else if (k === "<") {
          const end = pattern.indexOf(">", i);
          if (end < 0) throw new Decline("an unterminated group name");
          name = decodeName(pattern.slice(i + 2, end));
          i = end + 1;
        } else throw new Decline("a group form not read (modifiers)");
      }
      if (capture) groups.push({ always: !optional, name });
      disjunction(optional || lookaround);
      if (at(i) !== ")") throw new Decline("an unterminated group");
      i++;
      if (lookaround) {
        maybeFrom(first);
        // A lookahead is quantifiable outside Unicode mode (Annex B); a
        // quantifier on one makes its groups maybe, as below.
      }
    } else if (c === ")") throw new Decline("an unbalanced parenthesis");
    else i++;
    const q = at(i);
    let min = 1, quantified = false;
    if (q === "*" || q === "?") { min = 0; quantified = true; i++; }
    else if (q === "+") { quantified = true; i++; }
    else if (q === "{") {
      const m = /^\{(\d+)(?:,(\d*))?\}/.exec(pattern.slice(i));
      if (m && m[1] !== undefined) { min = Number(m[1]); quantified = true; i += m[0].length; }
      else if (unicode) throw new Decline("a lone brace");
    }
    if (quantified) {
      if (at(i) === "?") i++;
      if (min === 0) maybeFrom(first);
    }
  };
  disjunction(false);
  if (i !== pattern.length) throw new Decline("unread input");
  return groups;
}

/** The host's count of groups and its group names, from its own compilation
 * of the pattern: an empty match of `P|` has every group unmatched. */
function hostDescriptor(pattern: string, flags: string): { count: number; names: string[] } {
  const match = new RegExp(`${pattern}|`, flags.replace(/[gy]/g, "")).exec("");
  if (!match) throw new Decline("the host found no empty match");
  return { count: match.length - 1, names: Object.keys(match.groups ?? {}).sort() };
}

/** The shape of `/pattern/flags`: the reading's, when it reads the pattern
 * and agrees with the host on the count and the names; else the conservative
 * shape, `null`. */
export function regexpShape(pattern: string, flags: string): RegExpShape | null {
  try {
    const groups = groupsOf(pattern, flags);
    const host = hostDescriptor(pattern, flags);
    const names = [...new Set(groups.flatMap(g => g.name === null ? [] : [g.name]))].sort();
    if (host.count !== groups.length || host.names.join("\u0000") !== names.join("\u0000")) return null;
    return { always: groups.map(g => g.always), named: names.length > 0, global: flags.includes("g") };
  } catch (error) {
    if (error instanceof Decline) return null;
    throw error;
  }
}

/** A literal's text, `/P/F`, as its pattern and flags. */
export function literalParts(text: string): { pattern: string; flags: string } {
  const cut = text.lastIndexOf("/");
  if (!text.startsWith("/") || cut <= 0) throw Error(`not a regular expression literal: ${text}`);
  return { pattern: text.slice(1, cut), flags: text.slice(cut + 1) };
}

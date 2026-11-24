// Two trees compared by an enum field of 64 members, then by their children.
// The comparison of the kinds tests each member in turn, so each path through
// it carries up to 64 disequalities when the closure's slots leave the store.
export enum Kind {
  K0,
  K1,
  K2,
  K3,
  K4,
  K5,
  K6,
  K7,
  K8,
  K9,
  K10,
  K11,
  K12,
  K13,
  K14,
  K15,
  K16,
  K17,
  K18,
  K19,
  K20,
  K21,
  K22,
  K23,
  K24,
  K25,
  K26,
  K27,
  K28,
  K29,
  K30,
  K31,
  K32,
  K33,
  K34,
  K35,
  K36,
  K37,
  K38,
  K39,
  K40,
  K41,
  K42,
  K43,
  K44,
  K45,
  K46,
  K47,
  K48,
  K49,
  K50,
  K51,
  K52,
  K53,
  K54,
  K55,
  K56,
  K57,
  K58,
  K59,
  K60,
  K61,
  K62,
  K63,
}
export type Tree = { kind: Kind; text: string; children: Tree[] };

export function sameTrees(x: Tree, y: Tree): boolean {
  const same = (a: Tree, b: Tree): boolean => {
    if (a.kind !== b.kind) return false;
    const as: Tree[] = [],
      bs: Tree[] = [];
    a.children.forEach((c) => void as.push(c));
    b.children.forEach((c) => void bs.push(c));
    if (!as.length && !bs.length) return a.text === b.text;
    return (
      as.length === bs.length &&
      as.every((c, i) => {
        const d = bs[i];
        return !!d && same(c, d);
      })
    );
  };
  return same(x, y);
}

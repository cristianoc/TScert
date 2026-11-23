// A call of review.ts's walker outside every function declaration: no
// unit's verdict carries its check of rule Inst, so the prototype refuses
// the walker (review.ts, walkImported).
import { walkImported } from "./review.js";

type Prepared = { widths: number[]; flags: number[] };

export const replaceAll = (p: Prepared): number => walkImported<'{}'>(p, () => { p.widths = []; });

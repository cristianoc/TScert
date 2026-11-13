// A gap at the entry check: the start proposes `xs.length === old(xs.length)`
// for the entry term the postcondition names, and the entry check entails it
// only where the entry facts state `xs.length` defined. `snapshot` states no
// precondition. Its type `number[]` defines the length in the model only at
// a positive budget, and an entry state is one of any budget, so the start
// does not know it from the type (ARITHMETIC.md, "Two-state postconditions").
/** @ensures result.length === old(xs.length) */
export function snapshot(xs: number[]): number[] { return xs; }

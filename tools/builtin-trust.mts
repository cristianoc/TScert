/**
 * **A built-in's trust fields** (SOURCE-CONTRACTS.md, "A built-in's trust
 * fields"): the trust rows on standard natives (the Read-only frames note,
 * the natives item; framed-acceptance.md, "Two trust rows on standard
 * natives"), stated clause by clause on every built-in's contract, each
 * value checked against the section of the specification `spec` cites.
 *
 * - `onThrow`, row (a): `"footprint"` where the built-in's own writes
 *   before a throw are within its normal-return footprint at every
 *   signature its contract states, `"top"` otherwise.
 * - `stores`, row (b): `"operands"` where, into storage that existed
 *   before its call, every run stores only primitives and values its
 *   receiver and arguments reach; `"other"` where some run stores another
 *   value there (`Error.captureStackTrace`).
 * - `callsArgs`, row (b): `"during"` where every run calls its function
 *   arguments only during the run; `"later"` where some run keeps one and
 *   calls it after the run returns (`setTimeout`).
 * - `passesOwnAllocations`: `true` where some run passes storage it
 *   allocates to a function argument (`JSON.stringify` with a replacer).
 *
 * The fields are checked when the contracts are loaded (`checkTrust`): a
 * contract missing one, or stating `onThrow` other than its effects state,
 * is refused. A built-in outside a clause of row (b) is read as outside
 * code (`outsideCode`).
 */
import type { CallEffect, TypeDefinition, TypeTerm } from "./declaration-types.mts";

export type BuiltinTrust = {
  readonly onThrow: "footprint" | "top";
  readonly stores: "operands" | "other";
  readonly callsArgs: "during" | "later";
  readonly passesOwnAllocations: boolean;
  readonly spec: string;
};

/** **A built-in within row (b)**: it stores only primitives and its
 * operands' values into existing storage, calls its function arguments
 * only during its run and passes none of its allocations to one; `onThrow`
 * as its effects state it. */
export const withinB = (spec: string, onThrow: BuiltinTrust["onThrow"]): BuiltinTrust =>
  ({ onThrow, stores: "operands", callsArgs: "during", passesOwnAllocations: false, spec });

/** **A built-in storing another value into existing storage**: within row
 * (b) but for `stores`. */
export const storesOther = (spec: string, onThrow: BuiltinTrust["onThrow"]): BuiltinTrust =>
  ({ ...withinB(spec, onThrow), stores: "other" });

/** **Whether a built-in is read as outside code**: its contract states it
 * outside a clause of row (b). */
export const outsideCode = (trust: BuiltinTrust): boolean =>
  trust.stores === "other" || trust.callsArgs === "later" || trust.passesOwnAllocations;

/** **Whether an effect bounds a throw by its normal-return frame**: its
 * exceptional exit's frame is its normal exit's. */
const throwWithinFootprint = (effect: CallEffect | undefined): boolean => effect !== undefined &&
  JSON.stringify(effect.exits.exceptional.frame) === JSON.stringify(effect.exits.normal.frame);

/** **The throw bound a built-in's effects state**: `"footprint"` where it
 * states at least one signature and each bounds a throw by its normal-return
 * frame, `"top"` otherwise. A built-in whose contract is computed (an
 * intrinsic built from its arguments) takes its `onThrow` from this. */
export const throwBound = (effects: readonly (CallEffect | undefined)[]): BuiltinTrust["onThrow"] =>
  effects.length > 0 && effects.every(throwWithinFootprint) ? "footprint" : "top";

/** **The check of a built-in's trust fields**, run when its contract is
 * loaded: each field present at one of its values, `spec` naming a section,
 * and `onThrow` `"footprint"` exactly where the contract states at least
 * one signature and each signature's effect (`undefined` where it states
 * none, its declaration's then bounding nothing) bounds a throw by its
 * normal-return frame. The refusal names the built-in and the field. */
export function checkTrust(name: string, trust: unknown, effects: readonly (CallEffect | undefined)[]): BuiltinTrust {
  const fail = (what: string): never => { throw Error(`the built-in ${name}'s contract ${what}`); };
  if (typeof trust !== "object" || trust === null) return fail("states no trust fields");
  const field = (key: string): unknown => key in trust ? (trust as Record<string, unknown>)[key] : fail(`states no ${key}`); // asserted: `key in trust` holds of an object
  const onThrow = field("onThrow"), stores = field("stores"), callsArgs = field("callsArgs");
  const passes = field("passesOwnAllocations"), spec = field("spec");
  if (onThrow !== "footprint" && onThrow !== "top") return fail(`states onThrow ${String(onThrow)}`);
  if (stores !== "operands" && stores !== "other") return fail(`states stores ${String(stores)}`);
  if (callsArgs !== "during" && callsArgs !== "later") return fail(`states callsArgs ${String(callsArgs)}`);
  if (typeof passes !== "boolean") return fail(`states passesOwnAllocations ${String(passes)}`);
  if (typeof spec !== "string" || spec.trim() === "") return fail("cites no section of a specification");
  const stated = throwBound(effects);
  if (onThrow !== stated) return fail(`states onThrow ${onThrow}, its effects ${stated}`);
  return { onThrow, stores, callsArgs, passesOwnAllocations: passes, spec };
}

/** The effects a method's type states: a signature's own, each part of an
 * intersection's, each signature of a scheme's; `undefined` for a type
 * stating no signature's effect. */
export const signatureEffects = (type: TypeTerm): (CallEffect | undefined)[] =>
  type.k === "function" || type.k === "constructor" ? [type.effect]
  : type.k === "intersection" ? type.parts.flatMap(signatureEffects)
  : type.k === "scheme" ? type.signatures.map(s => s.effect) : [undefined];

/** Whether a member's type is a method's: a signature, a scheme, or an
 * intersection with one among its parts. */
const isMethod = (type: TypeTerm): boolean => type.k === "function" || type.k === "scheme" ||
  (type.k === "intersection" && type.parts.some(isMethod));

/** **The methods a stated type states**, by `Declaration.member`: each
 * method-typed member of the object types its equation states, an
 * intersection's parts included, with the effects its signatures state. A
 * reference among an intersection's parts is another definition's, whose
 * methods are its own. */
export function statedMethods(definition: TypeDefinition): { name: string; effects: (CallEffect | undefined)[] }[] {
  const methods: { name: string; effects: (CallEffect | undefined)[] }[] = [];
  const walk = (type: TypeTerm): void => {
    if (type.k === "intersection") { type.parts.forEach(walk); return; }
    if (type.k !== "object") return;
    for (const field of type.fields)
      if (isMethod(field.type))
        methods.push({ name: `${definition.declaration.name}.${String(field.name)}`, effects: signatureEffects(field.type) });
  };
  if (definition.expression) walk(definition.expression);
  return methods;
}

/** **The check of stated types' trust fields**, run when the definitions
 * are loaded: every method each definition states has its entry in `table`,
 * checked at its effects (`checkTrust`), and every entry of `table` names
 * such a method. */
export function checkStatedTrust(definitions: readonly TypeDefinition[], table: ReadonlyMap<string, BuiltinTrust>): void {
  const named = new Set<string>();
  for (const definition of definitions)
    for (const { name, effects } of statedMethods(definition)) {
      checkTrust(name, table.get(name), effects);
      named.add(name);
    }
  for (const name of table.keys())
    if (!named.has(name)) throw Error(`the trust fields of ${name} name no method a stated type states`);
}

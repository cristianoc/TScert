// Census functions:
// declaration-graph.mts#promisedBinders
// declaration-graph.mts#promisedMethods
import type {
  SourceTypeParameter,
  TypeTerm,
} from "../../tools/declaration-types.mts";
type Binder = SourceTypeParameter<TypeTerm>;
export function binders(bs: Binder[], term: TypeTerm): Binder[] {
  return bs.map(
    (b): Binder =>
      b.bound === null
        ? b
        : {
            ...b,
            bound: {
              k: "intersection",
              span: b.bound.span,
              parts: [b.bound, term],
            },
          },
  );
}

type SchemeBinder = Extract<TypeTerm, { k: "scheme" }>["binders"][number];
export function methodBinders(
  bs: SchemeBinder[],
  term: TypeTerm,
): SchemeBinder[] {
  return bs.map(
    (b): SchemeBinder =>
      b.bound === null
        ? b
        : {
            ...b,
            bound: {
              k: "intersection",
              span: b.bound.span,
              parts: [b.bound, term],
            },
          },
  );
}

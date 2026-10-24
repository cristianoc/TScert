/* Part of the trusted front end (fragment-parse.mts): user-defined type guards
 * (`x is T`) and assertion functions (`asserts x is T`).
 *
 * A guard's result annotation states a promise about one parameter, which
 * TypeScript does not check. The function is read at its plain result,
 * `boolean` (`void`), with the promise beside it (`Guard`): its type carries
 * a promise signature, which the verifier proves at the body and a call
 * consumes (SOURCE-CONTRACTS.md, user-defined guards). The predicate is read
 * as the type reader reads one in any signature (`promiseOf`). */
import * as ts from "typescript/unstable/ast";
import type { ArrowFunction, FunctionDeclaration, FunctionExpression, MethodDeclaration } from "typescript/unstable/ast";
import type { TypeTerm } from "./declaration-types.mts";
import type { Guard } from "./fragment.mts";
import type { Gate } from "./fragment-parse.mts";
import { promiseOf } from "./type-term.mts";

/** The promise a function's result annotation states, or null where it states
 * none. */
export function guardOf(this: Gate, node: FunctionDeclaration | ArrowFunction | FunctionExpression | MethodDeclaration): Within<{ value: "any"; store: "grow" }, Guard | null> {
  const gate: Gate = this;
  const p = node.type;
  if (!p || !ts.isTypePredicateNode(p)) return null;
  const head = node.parameters[0];
  const ordinary = head && ts.isIdentifier(head.name) && head.name.text === "this" ? node.parameters.slice(1) : [...node.parameters];
  const { effect, type } = promiseOf(gate.scope, p, ordinary);
  const promise = effect.promise;
  if (promise === null) throw Error("internal: a type predicate without a promise");
  return "guards" in promise ? { param: promise.guards.param, asserts: false, type, span: gate.span(p) }
    : { param: promise.asserts.param, asserts: true, type, span: gate.span(p) };
}

/** The plain result a guard is called at: a type guard's `boolean`, an
 * assertion function's `void`. */
export function guardResult(guard: Guard): Within<{ value: "any"; store: "grow" }, TypeTerm> {
  return { k: "atom", name: guard.asserts ? "void" : "boolean", span: guard.span };
}

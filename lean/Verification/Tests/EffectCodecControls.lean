import Verification.Source.EffectCodec
import Verification.Programs.CodeConditions

/-! # Controls of the serialized effect at consumers no document reaches

A document in the grammar decodes, and the consuming check refuses it, for
the consumers no forged document reaches through the verifier's command
line. The others are controls of `tests/single-pass-controls.mts` ("forged
effect": coverage of a noncanonical transport; a rest closure's statement
past its scope or reading through a path).

- A second signature certifying an image stable, at a conjunction
  (`Effect.meetCovers`): the conjunction is read only by a `combine`
  certificate, which the arrow search proposes where no single signature of
  a value covers a target of fixed result. TypeScript admits such a value
  only where one of its signatures alone is assignable, and the targets of
  the native values the cases pass are callbacks whose result is inferred
  from the value's signatures (`map`'s) or `unknown` (`filter`'s), so no
  case's run reaches it; a forged document would need a case passing a
  declared value to a parameter of fixed function type. A stable image
  is the one world-dependent formula a document states: the reader refuses
  an assertion reference.
- An exceptional postcondition and an exit position past the arity, at a
  code's obligations (`exportsEstablished`, `Effect.belowRow`): a code's
  signature is read from a statement or a claim, whose readers admit closed
  frames, spine regions and a fresh result (`freshSpine 0`) alone. -/
namespace Verification.Tests.EffectCodecControls
open Lean Verification CallEffects

private def decoded (text : String) : Option Effect :=
  match Json.parse text with
  | .ok j => (EffectCodec.decode j).toOption
  | .error _ => none

private def withNormal (frame ensures : String) : String :=
  "{\"exits\":{\"normal\":{\"frame\":" ++ frame ++ ",\"ensures\":" ++ ensures ++
    "},\"exceptional\":{\"frame\":[],\"ensures\":[]}},\"promise\":null,\"requires\":null,\"pre\":[]}"

private def withExceptional (ensures : String) : String :=
  "{\"exits\":{\"normal\":{\"frame\":[],\"ensures\":[]},\"exceptional\":{\"frame\":[],\"ensures\":" ++ ensures ++
    "}},\"promise\":null,\"requires\":null,\"pre\":[]}"

private def stableImage : String := withNormal "[]" "[{\"and\":{\"left\":\"truth\",\"right\":{\"transport\":{\"shift\":1,\"overrides\":[],\"boxed\":true,\"stable\":[1]}}}}]"
private def thrownPost : String := withExceptional "[{\"operation\":{\"post\":{\"freshSpine\":{\"x\":0}}}}]"
private def farExit : String := withNormal "[]" "[{\"operation\":{\"post\":{\"freshSpine\":{\"x\":4}}}}]"

-- A second signature whose exit certifies an image stable reads its world:
-- the conjunction refuses it, at any nesting.
#guard (decoded stableImage).isSome
#guard (decoded stableImage).all fun b => !Effect.meetCovers Effect.ordinary b Effect.ordinary
-- A postcondition of the exceptional exit, which no run of a rest body
-- establishes: the body's obligations refuse it.
#guard (decoded thrownPost).all fun e => !ProgramTyping.exportsEstablished e []
-- An exit position past a callable of one actual: its scope refuses it.
#guard (decoded farExit).all fun e => !e.belowRow 1
#guard (decoded farExit).all fun e => e.belowRow 4

end Verification.Tests.EffectCodecControls

import Verification.Source.EffectCodec
import Verification.Programs.CodeConditions

/-! # Controls of the serialized effect at its consumers

A document in the grammar decodes, and the check that reads the property a
decoder does not establish refuses it: a noncanonical transport at
coverage, a second signature whose exit reads its world at a conjunction,
an image certified stable at a conjunction, an exported postcondition a
run does not establish and a frame reading the heap beyond a location at
the obligations of a body composed across its rest allocation, and
positions outside a callable's arity at its scope. -/
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

private def canonical : String := withNormal "[]" "[{\"transport\":{\"shift\":1,\"overrides\":[[3,{\"path\":{\"root\":0,\"fields\":[]}}]],\"boxed\":false,\"stable\":[]}}]"
private def shifted : String := withNormal "[]" "[{\"transport\":{\"shift\":2,\"overrides\":[],\"boxed\":false,\"stable\":[]}}]"
private def stableImage : String := withNormal "[]" "[{\"and\":{\"left\":\"truth\",\"right\":{\"transport\":{\"shift\":1,\"overrides\":[],\"boxed\":true,\"stable\":[1]}}}}]"
private def thrownPost : String := withExceptional "[{\"operation\":{\"post\":{\"freshStore\":{\"x\":0}}}}]"
private def pathFrame : String := withNormal "[{\"region\":{\"path\":{\"x\":1,\"fields\":[\"f\"],\"key\":\"[]\"}},\"change\":\"any\"}]" "[]"
private def farEntry : String := withNormal "[{\"region\":{\"own\":{\"x\":3}},\"change\":\"any\"}]" "[]"
private def farExit : String := withNormal "[]" "[{\"operation\":{\"post\":{\"freshStore\":{\"x\":4}}}}]"

-- A canonical transport covers itself; a structurally valid transport of
-- shift 2 decodes, and coverage refuses it.
#guard (decoded canonical).any fun e => e.covers e
#guard (decoded shifted).isSome
#guard (decoded shifted).all fun e => !e.covers e
-- A second signature whose exit certifies an image stable reads its world:
-- the conjunction refuses it, at any nesting.
#guard (decoded stableImage).isSome
#guard (decoded stableImage).all fun b => !Effect.meetCovers Effect.ordinary b Effect.ordinary
-- A postcondition of the exceptional exit, which no run of a rest body
-- establishes, and a frame reading a path's store, which an allocation
-- before the call can move: the body's obligations refuse both.
#guard (decoded thrownPost).all fun e => !ProgramTyping.exportsEstablished e []
#guard (decoded pathFrame).all fun e => !ProgramTyping.framesAtLocation e
-- Entry and exit positions past a callable of one actual: its scope refuses
-- them.
#guard (decoded farEntry).all fun e => !e.belowRow 1
#guard (decoded farExit).all fun e => !e.belowRow 1
#guard (decoded farExit).all fun e => e.belowRow 4

end Verification.Tests.EffectCodecControls

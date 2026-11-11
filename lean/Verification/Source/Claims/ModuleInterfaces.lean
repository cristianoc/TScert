import Verification.Source.Claims.FragmentFront

/-! Closed component results consumed at the stage-store replay boundary. -/
namespace Verification.SourceClaimJson
open Lean ProgramTyping SourceExtraction

/-- The complete module wire document represented by a decoded module. -/
def interfaceModuleJson (m : Fragment.ModuleAst) : Json :=
  Json.mkObj [("location", toJson m.location), ("sourceSha256", toJson m.sourceSha256),
    ("declarations", m.document.getObjValD "declarations"), ("init", m.document.getObjValD "init"),
    ("functions", m.document.getObjValD "functions"), ("absent", toJson (m.absent.map fun (n, p, r) =>
      Json.mkObj [("name", toJson n), ("namePos", toJson p), ("reason", toJson r)]))]

/-- One projection per module, including an ordinary row for every function
whose stronger footprint has no closed check. -/
def encodeInterfaces (modules : List Fragment.ModuleAst) (est : Established) : Except String Json := do
  let rows ← modules.mapM fun m => do
    let entries ← (← jArr m.document "functions").mapM fun f => do
      let n ← f.getObjValAs? String "name"
      let p ← jField f "namePos"
      let value := match est.lookup (m.location, n) with
        | none => Json.null
        | some ((fp, ot, ret), u) => Json.mkObj [("footprint", toJson fp), ("onThrow", toJson ot),
            ("resultFootprint", toJson ret), ("unit", toJson u)]
      return Json.mkObj [("name", toJson n), ("namePos", p), ("established", value)]
    return Json.mkObj [("module", interfaceModuleJson m), ("entries", toJson entries)]
  return Json.mkObj [("modules", toJson rows)]

/-- Decode a store-authorized result, requiring its exact shape and each
complete module document to match the importing fragment. -/
def decodeInterfaces (sc : ImportScope) (j : Json) : Except String Established := do
  fieldsExactly j ["modules"]
  let mut seen : List String := []
  let mut out : Established := []
  for row in ← jArr j "modules" do
    fieldsExactly row ["module", "entries"]
    let m ← Fragment.decodeModule (← jField row "module")
    if seen.contains m.location then throw "duplicate interface module"
    seen := seen ++ [m.location]
    let some expected := sc.modules.find? (·.location == m.location)
      | throw s!"interface of unknown module {m.location}"
    if interfaceModuleJson expected != interfaceModuleJson m then throw s!"stale interface: {m.location}"
    let fs ← jArr m.document "functions"
    let entries ← jArr row "entries"
    if entries.length != fs.length then throw "incomplete interface"
    for (entry, f) in entries.zip fs do
      fieldsExactly entry ["name", "namePos", "established"]
      let n ← entry.getObjValAs? String "name"
      if n != (← f.getObjValAs? String "name") || (← jField entry "namePos") != (← jField f "namePos") then
        throw "interface function identity mismatch"
      let e ← jField entry "established"
      if e == Json.null then continue
      fieldsExactly e ["footprint", "onThrow", "resultFootprint", "unit"]
      let fp : Footprints.Closed ← fromJson? (← jField e "footprint")
      let ot ← e.getObjValAs? Bool "onThrow"
      let ret : Footprints.Closed ← fromJson? (← jField e "resultFootprint")
      let u ← e.getObjValAs? String "unit"
      if !u.startsWith s!"module:{m.location}#" then throw "interface group identity mismatch"
      out := out ++ [((m.location, n), (fp, ot, ret), u)]
  return out

/-- Dependency discovery and canonical SCC order, shared with direct use. -/
def interfacePlan (ast : Json) : Except String Json := do
  let sc ← ImportScope.of ast
  let needs ← interfaceNeeds sc
  let components := (interfaceComponents needs).map fun c =>
    let dependencies := ((c.flatMap fun n => n.reads.map (·.location)).eraseDups.filter
      fun l => !c.any (·.module.location == l)).mergeSort (· ≤ ·)
    Json.mkObj [("modules", toJson (c.map fun n => interfaceModuleJson n.module)),
      ("dependencies", toJson dependencies)]
  return Json.mkObj [("components", toJson components)]

end Verification.SourceClaimJson

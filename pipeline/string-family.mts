// The string-tagged stand-in family's description (HOST-FAMILIES.md, "A
// string-tagged stand-in"): the whole of what activates the stand-in package
// `pipeline/string-family-fixture/`, its installation the package Node finds
// from `pipeline/string-family-fixture-project/` (pipeline/fixture-links.mts).
// Its guard table is the generator's output (`dev/guard-table.mts`), which
// `tests/host-families.mts` compares with it. Test data: no entry point of
// the pipeline activates it.
import type { FamilyDescription } from "../tools/host-families.mts";

export const stringFamily: FamilyDescription = {
  package: { name: "string-family-fixture", version: "1.0.0" },
  installation: { from: "pipeline/string-family-fixture-project",
    digest: "9c12a1ea6dc3576cfdb24ac1d957be617209fefb29aba00ef6347e6e308659cc" },
  marker: "StringFixture",
  root: { name: "Unit", form: "inheritance", text: "export interface Unit {" },
  tag: { field: "type", primitive: "string", constants: { enum: "UnitType" } },
  table: [{ rule: "literal" }],
  corrections: [],
  omitted: [],
  stable: { excluded: [] },
  guards: {
    entryPoint: "./ast",
    conditions: ["node", "import", "module-sync", "node-addons", "default"],
    entryModule: "ast.js",
    closure: {
      files: {
        "ast.js": "ec36559dd989abd248cf999d4c3b2bb750799046b0d88b1630a9d53a3ad0056c",
        "kinds.js": "7cb37e251aae0c597bb7f572bd109efb935cc15860ae9e892521adf431f70e6d",
      },
      edges: [["ast.js", "UnitType", "kinds.js", "UnitType", [], "import"]],
    },
    helpers: {
      "ast.js#isExpressionKind": "function isExpressionKind(type) {\n    return type === UnitType.Name\n        || type === UnitType.Call;\n}",
    },
    guards: [
      { name: "isExpression", kind: "node", domain: "Unit", tags: ["Call", "Name"], module: "ast.js",
        helpers: ["ast.js#isExpressionKind"], edges: [["ast.js", "UnitType", "kinds.js", "UnitType"]],
        text: "export function isExpression(node) {\n    return isExpressionKind(node.type);\n}" },
      { name: "isName", kind: "node", domain: "Unit", tags: ["Name"], module: "ast.js",
        helpers: [], edges: [["ast.js", "UnitType", "kinds.js", "UnitType"]],
        text: "export function isName(node) {\n    return node.type === UnitType.Name;\n}" },
    ],
    excluded: [["isNameLoosely", "isNameLoosely takes 2 parameters"]],
  },
};

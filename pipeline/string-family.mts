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
    digest: "a40b3afc6790a1d1632711cc81ab2104af62cb005bb434580b83cd0bcc18a6d3" },
  marker: "StringFixture",
  root: { name: "Unit", form: "inheritance", text: "export interface Unit {" },
  tag: { field: "type", primitive: "string", constants: { enum: "UnitType" } },
  table: [{ rule: "literal" }],
  corrections: [],
  omitted: [],
  footprints: [],
  stable: { excluded: [] },
  // Both kinds' audited behaviour on `undefined`: a node guard throws, a tag
  // guard of equalities answers `false`.
  undefinedInputs: ["node", "tag"],
  guards: {
    entryPoint: "./ast",
    conditions: ["node", "import", "module-sync", "node-addons", "default"],
    entryModule: "ast.js",
    closure: {
      files: {
        "ast.js": "1b6a28bf5c5ce65f9087f22df09b628db3fad34bcdbac4de95bfd6ad8181c38f",
        "kinds.js": "7cb37e251aae0c597bb7f572bd109efb935cc15860ae9e892521adf431f70e6d",
      },
      edges: [["ast.js", "UnitType", "kinds.js", "UnitType", [], "import"]],
    },
    helpers: [
      ["ast.js#isExpressionKind", "function isExpressionKind(type) {\n    return type === UnitType.Name\n        || type === UnitType.Call;\n}"],
    ],
    guards: [
      { name: "isExpression", kind: "node", domain: "Unit", tags: ["Call", "Name"], onUndefined: "throws", module: "ast.js",
        helpers: ["ast.js#isExpressionKind"], edges: [["ast.js", "UnitType", "kinds.js", "UnitType"]],
        text: "export function isExpression(node) {\n    return isExpressionKind(node.type);\n}" },
      { name: "isName", kind: "node", domain: "Unit", tags: ["Name"], onUndefined: "throws", module: "ast.js",
        helpers: [], edges: [["ast.js", "UnitType", "kinds.js", "UnitType"]],
        text: "export function isName(node) {\n    return node.type === UnitType.Name;\n}" },
      { name: "isNameType", kind: "tag", domain: "UnitType", tags: ["Name"], onUndefined: "false", module: "ast.js",
        helpers: [], edges: [["ast.js", "UnitType", "kinds.js", "UnitType"]],
        text: "export function isNameType(type) {\n    return type === UnitType.Name;\n}" },
    ],
    excluded: [
      ["isCallAfterConstant", "isCallAfterConstant declares a constant"],
      ["isConstantType", "isConstantType compares UnitType.Name === UnitType.Name, not its argument with a constant"],
      ["isNameLoosely", "isNameLoosely takes 2 parameters"],
      ["isNameOfConstant", "isNameOfConstant calls isNameType on a constant"],
      ["isNameOptional", "isNameOptional reads an optional chain"],
      ["isNameOrAbsent", "isNameOrAbsent reads node"],
      ["isParenthesizedType", "isParenthesizedType compares (UnitType.Name) === UnitType.Name, not its argument with a constant"],
      ["isSameType", "isSameType compares type === type, not its argument with a constant"],
    ],
  },
};

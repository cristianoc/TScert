// The question-dot token of a tagged template is a field the declarations state required and the runtime
// leaves absent (COMPILER-API.md, "Corrections"): its reading is optional,
// so it is no `QuestionDotToken`. Under Node, on tag`a`, the function returns
// `undefined`.
import * as ts from "typescript/unstable/ast";

export function read(t: ts.TaggedTemplateExpression): ts.QuestionDotToken {
  return t.questionDotToken;
}

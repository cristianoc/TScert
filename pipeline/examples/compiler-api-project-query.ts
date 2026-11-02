// The client starts with an API satisfying COMPILER-API.md's T6 and T8.
// Construction is outside this checked client. Requests, returned handles,
// immutable node lists and normal-return effects use existing contracts.
import type { API } from "typescript/unstable/sync";
export function statementTypeFlags(
  api: API,
  config: string,
  file: string,
): number[] {
  const snapshot = api.updateSnapshot({ openProject: config });
  try {
    const project = snapshot.getProject(config);
    if (!project) return [];
    const source = project.program.getSourceFile(file);
    if (!source) return [];
    return source.statements.map(
      (node) => project.checker.getTypeAtLocation(node)?.flags ?? 0,
    );
  } finally {
    snapshot.dispose();
  }
}

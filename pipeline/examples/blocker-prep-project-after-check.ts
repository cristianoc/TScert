// Census functions:
// declaration-graph.mts#withProject
// declaration-graph.mts#useProject
// declaration-graph.mts#withOwnProject
// declaration-graph.mts#clientErrors
import type { Project } from "typescript/unstable/sync";
export function use(
  project: Project | undefined,
  check: (p: Project) => void,
): string {
  if (!project?.configFileName || !project.compilerOptions.strict)
    throw Error("strict project required");
  check(project);
  return project.configFileName;
}

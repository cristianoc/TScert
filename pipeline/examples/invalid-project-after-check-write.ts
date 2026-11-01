export function use(
  project: { options: { strict?: boolean } } | undefined,
  check: (p: { options: { strict?: boolean } }) => void,
): true {
  if (!project || !project.options.strict) throw Error("strict required");
  check(project);
  return project.options.strict;
}

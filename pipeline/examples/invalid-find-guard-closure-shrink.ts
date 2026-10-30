// A guard closure passed to `find` that shrinks the array `find` searches:
// `find` visits every index below the length it read first, so once the
// closure pops the array it is called at `undefined`, where its parameter
// promises a statement, and reading its `kind` throws (run under Node).
type Declaration = { kind: "declaration"; body: boolean };
type Other = { kind: "other" };

const statements: (Declaration | Other)[] = [
  { kind: "other" },
  { kind: "declaration", body: true },
];

export function first(): boolean {
  const found = statements.find((d): d is Declaration => {
    statements.pop();
    return d.kind === "declaration";
  });
  return found ? found.body : false;
}

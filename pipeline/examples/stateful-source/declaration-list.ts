// Several bindings in one declaration. The initializers evaluate left to
// right, each later one seeing the earlier bindings, under one statement
// entry: the producer states no cut between the declarators.
function earlierBinding(): number {
  const seed = 2,
    second = seed;
  return second;
}

// A `let` list allocates one cell per binding. The second initializer copies
// the first cell's contents, so a later write to the first does not reach it.
function laterWriteStaysSeparate(seed: boolean | null): boolean {
  let first: boolean | null = seed,
    second: boolean | null = first;
  first = null;
  if (second !== null) return second;
  return false;
}

// A later initializer may write an earlier binding of the same declaration.
// The write happens before the statement completes.
function effectInLaterInitializer(): null {
  let first: number | null = 1,
    second = (first = null);
  return first;
}

// Inferred `let` contracts come from the following statement's entry, for
// every binding of the list.
function inferredContracts(): number {
  let first = 1,
    second = first;
  first = 2;
  return second;
}

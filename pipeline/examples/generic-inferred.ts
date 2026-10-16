function inferred<T>(value: T): T {
  const saved = value;
  return saved;
}

function inferredChain<T, U extends T>(value: U): T {
  const first = value,
    second = first;
  return second;
}

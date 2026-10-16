/** The receiver expression runs before ordinary arguments, even for arrows. */
function receiverCall(seed: boolean): boolean {
  const f = Object.assign<
    (first: boolean, second: boolean) => boolean,
    { value: boolean }
  >((first: boolean, second: boolean): boolean => (first ? second : !second), {
    value: seed,
  });
  const alias = f;
  return alias.call((alias.value = !seed), alias.value, seed);
}

/** A captured local arrow stays eligible; its nullary call sees the write. */
function capturedReceiverCall(seed: boolean): boolean {
  const cell = { value: seed };
  const target = (): boolean => cell.value;
  return ((): boolean => target.call((cell.value = !seed)))();
}

// A closure can capture the later binding, but invoking it during that
// binding's initializer must still hit the temporal dead zone.
function defaultInvokedTooEarly(): boolean {
  const pick = (
    read: () => boolean = (): boolean => later,
    later: boolean = read(),
  ): boolean => read();
  return pick();
}

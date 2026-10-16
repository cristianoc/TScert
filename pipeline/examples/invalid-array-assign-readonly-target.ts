// A readonly field is no writable location.
function wrong(box: { readonly slot: number }): void {
  // @ts-expect-error Cannot assign to 'slot' because it is a read-only property
  [box.slot] = [1];
}

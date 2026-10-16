function writeThroughView(view: { readonly value: number }): number {
  view.value = 2;
  return view.value;
}

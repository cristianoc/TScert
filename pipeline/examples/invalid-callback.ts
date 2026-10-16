function wrongCallback(f: (x: boolean) => boolean): boolean {
  return f(null);
}

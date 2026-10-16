function branches(flag: boolean, value: number): number {
  if (flag) {
    const doubled = value + value;
    return doubled;
  } else {
    return value;
  }
}

// A primitive method's empty footprint does not cover its argument's call.
export function drop(segments: string[]): number {
  segments.pop();
  return 0;
}

export function first(segments: string[]): string {
  if (segments.length > 0) {
    if (segments[0]!.charCodeAt(drop(segments)) === 173) return "";
    return segments[0]!;
  }
  return "";
}

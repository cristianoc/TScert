// A write to an opaque URL must be refused independently of member reads.
export function moved(url: URL): void {
  url.href = "http://example.com/a";
}

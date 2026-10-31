// forEach through an optional object field after a test.
// Census functions:
// diagnostic.mts#readDiagnostic
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
function isRecord(v: Json | undefined): v is Fields {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
export function diagnostic(
  destination: Fields,
  available: Json[],
  labels: (v: Json, ...further: unknown[]) => void,
): void {
  const claim = destination.claim;
  if (!isRecord(claim)) return;
  const context = claim.context;
  if (!Array.isArray(context)) return;
  available.forEach(labels);
  context.forEach(labels);
}

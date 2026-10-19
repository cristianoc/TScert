// Global functions a project declares for its host, outside any installed
// package: `hostNow`, which no reviewed entry lists, and an overload of
// Node's `clearTimeout` whose text differs from the one reviewed.
declare function hostNow(): number;
declare function clearTimeout(timeout: number): void;

// `import.meta.url` copies the url of the module's wrapper, which other code
// reaches through `require.cache` and may set to a number.
export function where(): string {
  return import.meta.url;
}

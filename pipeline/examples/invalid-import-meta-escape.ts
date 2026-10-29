// `import.meta` handed to other code, which writes a number at `url`.
export function leaked(write: (meta: object) => void): string {
  write(import.meta);
  return import.meta.url;
}

// Census: compiler-channel.mts#current, #profile, #identify, #launcher, #useInstallationForTests.
type Identity = { [field: string]: string | boolean };
type Identification =
  | { identity: Identity; unobserved?: never }
  | { unobserved: string };
type Implementation =
  | { identity: Identity; changed: () => boolean; unobserved?: never }
  | { unobserved: string; identity?: never };
type Current = {
  installation: string;
  implementation: Implementation;
  launcher: string | null;
};
export function current(
  installation: string,
  identified: Identification,
): Current {
  return {
    installation,
    launcher: null,
    implementation:
      identified.unobserved !== undefined
        ? identified
        : { identity: identified.identity, changed: (): boolean => false },
  };
}

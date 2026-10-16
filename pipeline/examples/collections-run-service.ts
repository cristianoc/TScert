// RunService: the service's type reaches Service's readonly
// optional `externalServices`, read here as present or undefined, and the
// options' type has optional fields.
import { runService } from "@fixture/collections";
import type { AnyService, ExternalService } from "@fixture/collections";
export async function start(
  service: AnyService,
  platform: "wasm" | "native",
): Promise<void> {
  await runService(service, {
    control_port: 3588,
    streaming_port: 3587,
    platform,
    no_cors: false,
  });
}
export function externals(
  service: AnyService,
): { readonly [name: string]: ExternalService } | undefined {
  return service.externalServices;
}

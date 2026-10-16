// RunService's `platform` is an optional field of "wasm" | "native": a field
// holding any string does not establish it.
import { runService, type Server } from "@fixture/collections";
import type { AnyService } from "@fixture/collections";
export function start(service: AnyService, platform: string): Promise<Server> {
  return runService(service, {
    control_port: 3588,
    streaming_port: 3587,
    platform,
    no_cors: false,
  });
}

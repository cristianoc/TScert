// Main: async/await, a module constant read from `process`, and a
// `for...of` over an array literal.
import { runService } from "@fixture/collections";
import type { AnyService } from "@fixture/collections";
const platform: "wasm" | "native" =
  process.env["APP_PLATFORM"] === "native" ? "native" : "wasm";
export async function main(service: AnyService): Promise<void> {
  const server = await runService(service, {
    control_port: 3588,
    streaming_port: 3587,
    platform,
  });
  const shutdown = async (): Promise<void> => {
    await server.close();
  };
  for (const sig of ["SIGTERM", "SIGINT"]) process.on(sig, shutdown);
}

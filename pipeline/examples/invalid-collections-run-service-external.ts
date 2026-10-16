// Service's `externalServices` is a readonly optional field: a service
// may lack it, so its read is not the dictionary alone.
import type { AnyService, ExternalService } from "@fixture/collections";
export function externals(service: AnyService): {
  readonly [name: string]: ExternalService;
} {
  return service.externalServices;
}

// Cross-module `.d.ts` imports of computed-type-bearing generic functions
// (`runService`, `initService`, `asLeader`, `asFollower`), abstract base
// classes, mapped-type bounds, and generic `ServiceInstance.reload`.
import {
  InputDefinition,
  asFollower,
  asLeader,
  initService,
  runService,
  type AbstractEagerCollection,
  type Context,
  type EagerCollection,
  type Json,
  type Resource,
  type SkipService,
} from "@fixture/mapped-service-api";

class Names
  implements Resource<{ readonly names: EagerCollection<string, string> }>
{
  constructor(_params: Json) {}
  instantiate(
    collections: { readonly names: EagerCollection<string, string> },
    _context: Context,
  ): AbstractEagerCollection {
    return collections.names;
  }
}

export async function start(): Promise<boolean> {
  const s1 = await runService({
    inputs: { names: new InputDefinition<string, string>([["a", ["x"]]]) },
    resources: { names: Names },
    createGraph: (ic) => ic,
  });
  const service: SkipService<
    { readonly names: InputDefinition<string, string> },
    { readonly names: EagerCollection<string, string> }
  > = {
    inputs: { names: new InputDefinition<string, string>([["b", ["y"]]]) },
    resources: { names: Names },
    createGraph: (ic) => ({ names: ic.names }),
  };
  const leader = asLeader(service);
  const follower = asFollower(service, {
    leader: { host: "localhost", streaming_port: 8080, control_port: 8081 },
    collections: ["names"],
  });
  const s2 = await runService(leader);
  const s3 = await runService(follower);
  const inst = await initService(service);
  await s1.close();
  await s2.close();
  await s3.close();
  return inst.running;
}

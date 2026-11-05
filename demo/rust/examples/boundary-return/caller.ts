import { next_id } from "./lib.js";

export function jobId(): bigint {
  return next_id();
}

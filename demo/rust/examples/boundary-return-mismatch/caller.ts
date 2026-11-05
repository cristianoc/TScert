import { next_id } from "./lib.js";

export function jobId(): number {
  return next_id();
}

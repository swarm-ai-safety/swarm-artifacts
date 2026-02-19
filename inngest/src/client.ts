/**
 * SWARM Research OS — Inngest client.
 *
 * Single source of truth for the typed Inngest client.
 * All functions import from here.
 */

import { EventSchemas, Inngest } from "inngest";
import type { Events } from "./events.js";

export const inngest = new Inngest({
  id: "swarm-research-os",
  schemas: new EventSchemas().fromRecord<Events>(),
});

/**
 * SWARM Research OS — Inngest HTTP server.
 *
 * Serves the Inngest functions via Express.
 * In production, this could be a Next.js route, Hono handler, etc.
 *
 * Usage:
 *   npx tsx src/serve.ts
 *   # Then in another terminal:
 *   npx inngest-cli@latest dev -u http://localhost:3000/api/inngest
 */

import express from "express";
import { serve } from "inngest/express";
import { inngest } from "./client.js";
import {
  validateRun,
  synthesizeSweep,
  synthesizeRedteam,
  retryRun,
  nightlyRegression,
  checkDrift,
  createResultsPR,
  postMerge,
  alertWeakened,
} from "./functions/index.js";

const app = express();
const port = parseInt(process.env.PORT ?? "3000", 10);

app.use(
  "/api/inngest",
  serve({
    client: inngest,
    functions: [
      validateRun,
      synthesizeSweep,
      synthesizeRedteam,
      retryRun,
      nightlyRegression,
      checkDrift,
      createResultsPR,
      postMerge,
      alertWeakened,
    ],
  }),
);

app.get("/health", (_req, res) => {
  res.json({ status: "ok", functions: 9 });
});

app.listen(port, () => {
  console.log(`SWARM Research OS Inngest server running on :${port}`);
  console.log(`Inngest endpoint: http://localhost:${port}/api/inngest`);
  console.log(`\nTo start the Inngest dev server:`);
  console.log(`  npx inngest-cli@latest dev -u http://localhost:${port}/api/inngest`);
});

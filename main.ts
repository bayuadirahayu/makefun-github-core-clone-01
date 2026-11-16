// Boot wrapper for the forge in app.ts.
//
// This file does only the trial lifecycle: start the forge on a kernel-chosen
// port, tell the suite where it listens, then wait until the suite says the
// trial is over and shut down. All of the forge behaviour lives in app.ts.
//
// The suite's side of the contract (see RULES.txt):
//   1. the forge binds an ephemeral port (port 0; never 8080, the suite's own)
//   2. this process POSTs {"port": <port>} to $MAKEFUN_ENV_URL/register
//      inside the 20-second boot budget
//   3. this process long-polls GET $MAKEFUN_ENV_URL/done until it answers
//      {"done": true}, then exits 0
// Nothing else in this file talks to the network.

import { createApp } from './app.ts';

// How long a single HTTP round trip to the suite may take before we give up
// on that attempt and retry it. The boot budget is 20 s, so a short timeout
// keeps a hung attempt from eating the whole budget.
const ROUND_TRIP_MS = 5_000;

// How long to wait between register attempts and between done polls.
const RETRY_PAUSE_MS = 500;
const DONE_POLL_MS = 1_000;

// The suite's origin, with any trailing slashes stripped so the paths below
// join cleanly. Missing entirely means we cannot run a trial at all.
const suiteOrigin = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
if (suiteOrigin === '') {
  process.stderr.write('[boot] MAKEFUN_ENV_URL is not set; nothing to register with\n');
  process.exit(1);
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/**
 * Announce the forge's port to the suite. The suite records the address this
 * request comes from and dials that address and port, so the request must go
 * out after the server is already listening. Returns true on a 2xx answer.
 */
async function announcePort(port: number): Promise<boolean> {
  let response: Response;
  try {
    response = await fetch(`${suiteOrigin}/register`, {
      method: 'POST',
      headers: { 'content-type': 'application/json' },
      body: JSON.stringify({ port }),
      signal: AbortSignal.timeout(ROUND_TRIP_MS),
    });
  } catch {
    return false;
  }
  return response.ok;
}

/**
 * Ask the suite once whether the trial is finished. Any transport hiccup or
 * unexpected body counts as "not done yet" — the loop below simply asks again
 * instead of dying on a transient failure mid-trial.
 */
async function trialFinished(): Promise<boolean> {
  let response: Response;
  try {
    response = await fetch(`${suiteOrigin}/done`, {
      method: 'GET',
      signal: AbortSignal.timeout(ROUND_TRIP_MS),
    });
  } catch {
    return false;
  }
  if (!response.ok) return false;
  let payload: unknown;
  try {
    payload = await response.json();
  } catch {
    return false;
  }
  return (
    payload !== null &&
    typeof payload === 'object' &&
    (payload as Record<string, unknown>).done === true
  );
}

/** Poll /done once a second until the suite reports the trial finished. */
async function waitUntilDone(): Promise<void> {
  for (;;) {
    if (await trialFinished()) return;
    await sleep(DONE_POLL_MS);
  }
}

/**
 * Start the forge, register it, then wait for the suite to finish.
 * Registration retries until it lands (or the process is killed by the boot
 * budget), because a single dropped request must not zero the trial.
 */
async function run(): Promise<void> {
  const forge = createApp();
  const port = await new Promise<number>((resolve, reject) => {
    forge.once('error', reject);
    // Port 0: the kernel picks a free ephemeral port. Binding 8080 would
    // collide with the suite itself, so it is never used.
    forge.listen(0, '0.0.0.0', () => {
      const address = forge.address();
      if (address === null || typeof address === 'string') {
        reject(new Error('server did not report a numeric address'));
        return;
      }
      resolve(address.port);
    });
  });

  for (;;) {
    if (await announcePort(port)) break;
    await sleep(RETRY_PAUSE_MS);
  }
  process.stderr.write(`[boot] forge listening on ${port}, registered with suite\n`);

  await waitUntilDone();

  // The suite has written its export; stop accepting and leave cleanly.
  await new Promise<void>((resolve) => forge.close(() => resolve()));
  process.stderr.write('[boot] suite done; shutting down\n');
}

run().catch((err: unknown) => {
  process.stderr.write(`[boot] fatal: ${err instanceof Error ? err.stack ?? err.message : String(err)}\n`);
  process.exit(1);
});

// Entry point for the forge: bind, register with the harness environment, then wait until the
// environment says the trial is over. The server itself lives in app.ts; this file only owns the
// lifecycle the harness expects (see wire.ts in the kit): an ephemeral port, a register POST, and a
// done poll. Nothing here imports anything beyond app.ts and the process environment.

import { createApp } from './app.ts';

const ENV = (process.env.MAKEFUN_ENV_URL ?? '').replace(/\/+$/, '');
if (ENV === '') {
  process.stderr.write('[entry] MAKEFUN_ENV_URL is not set\n');
  process.exit(1);
}

const FETCH_TIMEOUT_MS = 30_000;
const BACKOFF_START_MS = 250;
const BACKOFF_MAX_MS = 2_000;

/** Pause for `ms` milliseconds. */
function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/** The backoff after `attempt` failed requests, capped at BACKOFF_MAX_MS. */
function backoffMs(attempt: number): number {
  return Math.min(BACKOFF_MAX_MS, BACKOFF_START_MS * 2 ** Math.min(attempt, 8));
}

/**
 * Keep calling `fn` until it reports success (true) or a fatal error (throw). Any other outcome
 * or a thrown retryable error waits with exponential backoff and tries again.
 */
async function retryUntil(fn: () => Promise<boolean>, fatal: (err: unknown) => boolean): Promise<void> {
  for (let attempt = 0; ; attempt += 1) {
    try {
      if (await fn()) return;
    } catch (err) {
      if (fatal(err)) throw err;
    }
    await sleep(backoffMs(attempt));
  }
}

async function register(port: number): Promise<void> {
  await retryUntil(
    async () => {
      const res = await fetch(`${ENV}/register`, {
        method: 'POST',
        headers: { 'content-type': 'application/json' },
        body: JSON.stringify({ port }),
        signal: AbortSignal.timeout(FETCH_TIMEOUT_MS),
      });
      if (res.status === 200 || res.status === 409) return true;
      if (res.status === 400 || res.status === 405) throw new Error(`register refused: HTTP ${res.status}`);
      return false;
    },
    (err) => err instanceof Error && err.message.startsWith('register refused:'),
  );
}

async function waitForDone(): Promise<void> {
  await retryUntil(
    async () => {
      try {
        const res = await fetch(`${ENV}/done`, { signal: AbortSignal.timeout(FETCH_TIMEOUT_MS) });
        if (!res.ok) return false;
        const body = (await res.json()) as { done?: unknown };
        return body.done === true;
      } catch {
        return false;
      }
    },
    () => false,
  );
}

async function main(): Promise<void> {
  const server = createApp();
  await new Promise<void>((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, () => resolve());
  });
  const address = server.address();
  if (address === null || typeof address === 'string') throw new Error('the server did not bind an ephemeral TCP port');
  process.stdout.write(`[entry] listening on port ${address.port}\n`);
  await register(address.port);
  process.stdout.write('[entry] registered; waiting for the env to say done\n');
  await waitForDone();
  server.close();
  process.stdout.write('[entry] done\n');
}

try {
  await main();
  process.exit(0);
} catch (err) {
  process.stderr.write(`[entry] ${err instanceof Error ? err.message : String(err)}\n`);
  process.exit(1);
}

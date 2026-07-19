import { publishJob } from './jobs/queue.js';

export async function launchRun(input: { actor: unknown; document: { source: string } }) {
  const run = { id: crypto.randomUUID(), status: 'queued', ...input };
  await publishJob({ type: 'ingest.requested', runId: run.id, source: input.document.source });
  return run;
}

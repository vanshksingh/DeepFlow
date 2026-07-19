export function recordRunStarted(runId: string) { return { metric: 'ingest.started', runId }; }
export function recordRunFailed(runId: string, error: unknown) { return { metric: 'ingest.failed', runId, error }; }
export function recordRunCompleted(runId: string) { return { metric: 'ingest.completed', runId }; }

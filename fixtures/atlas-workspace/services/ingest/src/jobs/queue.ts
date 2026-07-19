export type IngestJob = { type: 'ingest.requested'; runId: string; source: string };
const jobs: IngestJob[] = [];
export async function publishJob(job: IngestJob) { jobs.push(job); }
export async function takeJob() { return jobs.shift(); }

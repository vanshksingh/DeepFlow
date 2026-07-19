import { takeJob } from '../jobs/queue.js';
import { fetchDocument } from './fetchSource.js';
import { parseByType } from './parseMime.js';
import { normalizeText, chunkText, embedChunks, saveRecord, emitIndexed } from '../../../../packages/data-core/src/index.js';

export async function handleIngest() {
  const job = await takeJob();
  if (!job) return;
  const response = await fetchDocument(job.source);
  const parsed = parseByType(response.type, response.body);
  const vectors = await embedChunks(chunkText(normalizeText(parsed)));
  await saveRecord({ runId: job.runId, vectors });
  await emitIndexed(job.runId);
}

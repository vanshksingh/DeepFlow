import { requireApiKey } from './auth.js';
import { launchRun } from '../../../services/ingest/src/ingestRun.js';

export async function startIngest(request: Request) {
  const actor = requireApiKey(request.headers.get('authorization'));
  const document = await request.json();
  return launchRun({ actor, document });
}

export function health() { return { ok: true }; }

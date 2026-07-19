import { writeDebugDump } from '../../../../packages/audit/src/debugDump.js';
export async function retryOrFail(error: unknown, source: string) {
  writeDebugDump({ error, source });
  throw error;
}

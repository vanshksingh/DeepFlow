export async function saveRecord(record: { runId: string; vectors: unknown[] }) { return { id: record.runId, count: record.vectors.length }; }

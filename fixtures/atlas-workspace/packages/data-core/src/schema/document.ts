export type DocumentInput = { source: string; content?: string; tags?: string[] };
export function assertDocument(input: DocumentInput) { if (!input.source) throw new Error('source is required'); return input; }
export function documentKey(input: DocumentInput) { return `${input.source}:${input.tags?.join(',') ?? ''}`; }

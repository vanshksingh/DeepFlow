export function rejectOversized(body: string, maxBytes = 1_000_000) { if (body.length > maxBytes) throw new Error('Document too large'); return body; }
export function rejectEmpty(body: string) { if (!body.trim()) throw new Error('Document is empty'); return body; }

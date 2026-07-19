const seen = new Map<string, number>();
export function enforceRateLimit(key: string) { const value = (seen.get(key) ?? 0) + 1; seen.set(key, value); if (value > 100) throw new Error('Rate limit exceeded'); }

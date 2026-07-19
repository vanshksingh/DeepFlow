export function chunkText(text: string, size = 300) { return Array.from({ length: Math.ceil(text.length / size) }, (_, i) => text.slice(i * size, (i + 1) * size)); }

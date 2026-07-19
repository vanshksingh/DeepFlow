export async function embedChunks(chunks: string[]) { return chunks.map((chunk, index) => ({ index, values: [chunk.length / 1000] })); }

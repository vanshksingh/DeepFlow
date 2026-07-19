export async function createEmbedding(text: string) { return [text.length / 1000, 0.1, 0.2]; }
export async function createEmbeddings(texts: string[]) { return Promise.all(texts.map(createEmbedding)); }

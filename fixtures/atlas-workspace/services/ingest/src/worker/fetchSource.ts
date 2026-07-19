import { retryOrFail } from './retryPolicy.js';

export async function fetchDocument(url: string) {
  try {
    const response = await fetch(url);
    if (!response.ok) throw new SourceUnavailableError(url, response.status);
    return { type: response.headers.get('content-type') ?? 'text/plain', body: await response.text() };
  } catch (error) { return retryOrFail(error, url); }
}
export class SourceUnavailableError extends Error { constructor(url: string, readonly status = 503) { super(`Source unavailable: ${url}`); } }

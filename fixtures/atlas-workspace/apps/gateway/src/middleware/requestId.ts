export function requestId(headers: Headers) { return headers.get('x-request-id') ?? crypto.randomUUID(); }
export function attachRequestId(request: Request) { return { request, requestId: requestId(request.headers) }; }

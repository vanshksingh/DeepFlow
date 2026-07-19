export const errorCatalog = { SOURCE_UNAVAILABLE: 'SOURCE_UNAVAILABLE', VECTOR_PROVIDER_DOWN: 'VECTOR_PROVIDER_DOWN' };
export function describeError(code: keyof typeof errorCatalog) { return errorCatalog[code]; }

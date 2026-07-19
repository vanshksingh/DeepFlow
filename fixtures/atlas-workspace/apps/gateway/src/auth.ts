export function requireApiKey(header: string | null) {
  if (!header?.startsWith('Bearer ')) throw new Error('Unauthenticated');
  return { keyId: header.slice(7) };
}

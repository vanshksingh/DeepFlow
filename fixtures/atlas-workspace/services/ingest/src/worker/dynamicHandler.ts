// Intentional dynamic boundary: static analysis cannot reliably resolve the handler.
export async function invokeNamedHandler(name: string, payload: unknown) {
  return (globalThis as any).handlers?.[name]?.(payload);
}

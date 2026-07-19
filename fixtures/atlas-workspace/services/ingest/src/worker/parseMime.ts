export function parseByType(type: string, value: string) {
  if (type.includes('json')) return JSON.stringify(JSON.parse(value));
  if (type.includes('html')) return value.replace(/<[^>]+>/g, ' ');
  return value;
}

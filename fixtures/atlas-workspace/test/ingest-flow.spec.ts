import { startIngest } from '../apps/gateway/src/documentRoutes.js';
export async function flowTest() { return startIngest({ headers: new Map(), json: async () => ({}) }); }

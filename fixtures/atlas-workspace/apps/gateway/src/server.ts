import { startIngest, health } from './documentRoutes.js';

export const routes = { 'POST /documents': startIngest, 'GET /health': health };

import { launchRun } from '../services/ingest/src/ingestRun.js';
export async function replay() { return launchRun({ actor: 'example', document: {} }); }

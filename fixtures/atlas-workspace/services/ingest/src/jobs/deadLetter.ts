export type DeadLetter = { runId: string; error: string };
export async function sendToDeadLetter(message: DeadLetter) { return message; }
export async function replayDeadLetter(message: DeadLetter) { return { ...message, replayed: true }; }

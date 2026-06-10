import { randomUUID } from 'node:crypto';

type SendReceiptRecord = {
  kind: 'report' | 'notice';
  email: string;
  test_id?: number;
  notice_id?: number;
  reg_no: string;
  student_name: string;
  message: string;
  wa_link: string;
  send_mode: string;
  expires_at: number;
};

const RECEIPT_TTL_MS = 30 * 60 * 1000;
const receipts = new Map<string, SendReceiptRecord>();

function cleanupExpiredReceipts() {
  const now = Date.now();
  for (const [token, payload] of receipts.entries()) {
    if (!payload || payload.expires_at < now) {
      receipts.delete(token);
    }
  }
}

export function createSendReceipt(payload: Omit<SendReceiptRecord, 'expires_at'>) {
  cleanupExpiredReceipts();
  const token = randomUUID();
  receipts.set(token, {
    ...payload,
    expires_at: Date.now() + RECEIPT_TTL_MS,
  });
  return token;
}

export function getSendReceipt(token: string) {
  cleanupExpiredReceipts();
  return receipts.get(String(token || '').trim()) || null;
}

export function deleteSendReceipt(token: string) {
  receipts.delete(String(token || '').trim());
}

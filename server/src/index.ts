import { createHash, randomUUID } from 'node:crypto';
import { spawn } from 'node:child_process';
import { copyFile, cp, mkdir, mkdtemp, readFile, readdir, rm, stat, unlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { dirname, extname, resolve } from 'node:path';
import { serve } from '@hono/node-server';
import { Hono, type Context } from 'hono';
import { cors } from 'hono/cors';
import { deleteCookie, getCookie, setCookie } from 'hono/cookie';
import JSZip from 'jszip';
import nodemailer from 'nodemailer';
import * as XLSX from 'xlsx';
import {
  APP_ENV_FILE,
  APP_NAME,
  APP_VERSION,
  ARCHIVE_DIR,
  BACKUP_DIR,
  CLIENT_ORIGIN,
  DEFAULT_SYSTEM_ADMIN_EMAIL,
  GOOGLE_STATE_COOKIE,
  LOGIN_OTP_COOKIE,
  NOTICE_UPLOAD_ROOT,
  PASSWORD_RESET_COOKIE,
  SERVER_HOST,
  SERVER_PORT,
  SERVER_ROOT,
  SESSION_COOKIE,
  SELF_RESET_OTP_COOKIE,
  TEST_MODE_COOKIE,
  SHINE_DB_PATH,
} from './lib/config.js';
import {
  addStudentsBulk,
  addNoticeAttachment,
  clearInactiveSessions,
  canCounselorAccessNotice,
  canCounselorAccessTest,
  canCounselorAccessStudent,
  checkpointAndCloseDatabase,
  checkUserAccess,
  createDepartment,
  createUser,
  createNotice,
  deleteAllCounselorStudents,
  deleteCounselorStudent,
  deleteTest,
  deleteDepartment,
  deleteNotice,
  deleteNoticeAttachment,
  deleteUser,
  findExistingDepartmentYearTest,
  forceLogoutUser,
  getBatchNameForYearLevel,
  getActiveSessionForUser,
  getActiveSessions,
  getAdminMessageStats,
  getAppConfig,
  getAllUniqueTests,
  getAllowedScopesForUser,
  getCounselorActivityForTest,
  getCounselorActivitySummary,
  getCounselorMessageHistory,
  getCounselorMessageStats,
  getCounselorSendNoticeRows,
  getCounselorSendReportRows,
  getDashboardMetrics,
  getDepartments,
  getNotice,
  getNoticeAttachmentByToken,
  getNoticeAttachments,
  getNoticeCompletionRows,
  getNoticeRecordsForActor,
  getNoticeSentRegNos,
  getNoticeScopePairs,
  getMessageCounselorSuggestions,
  getMessageDays,
  getMessageHistoryFiltered,
  getSentRegNosForTest,
  getSessionHistory,
  getSessionStatistics,
  getStudentCountForCounselor,
  getStudentMarksForRegForCounselor,
  getStudentsForCounselor,
  getTestMarksGrouped,
  getTestMarksGroupedForCounselor,
  getTestMetadata,
  getVisibleNoticesForCounselor,
  getVisibleReportSubjects,
  getVisibleTestCountForCounselor,
  getVisibleTestsForCounselor,
  getUserByEmail,
  getUserByIdentifier,
  getUsersForActor,
  getScopesForUser,
  logMessage,
  logNoticeDelivery,
  listUsersForActor,
  lockCounselorsForDepartment,
  lockUser,
  logoutAllUsers,
  logoutSession,
  normalizeAllowedTestName,
  renameUserEmail,
  reconnectDatabase,
  registerSession,
  saveUploadedTestMarks,
  saveCounselorStudent,
  setChiefAdminScopes,
  toAuthUser,
  toggleDepartment,
  unlockCounselorsForDepartment,
  updateAppConfig,
  updateAppConfigBulk,
  updateTestBlockStatus,
  updateTestMetadataFields,
  updateUser,
  updateUserPassword,
  unlockUser,
  upsertTestMark,
  upsertCounselorMarkOverride,
  updateDepartment,
  updateNotice,
  validateSession,
  verifyPassword,
  deleteMessageById,
  deleteMessagesByIds,
  db,
} from './lib/db.js';
import { buildParentMessage, buildParentSubjectsTable, fillTemplate, getWhatsappLink } from './lib/messaging.js';
import { buildGoogleOauthClientRedirect, buildGoogleOauthRedirectUri, getGoogleOauthSettings } from './lib/oauth.js';
import {
  clearDrivePath,
  deleteDriveFileFromPath,
  downloadDriveFileFromPath,
  findDrivePath,
  getGoogleDriveSettings,
  listDriveEntriesInPath,
  listDriveFilesInPath,
  uploadDriveFileToPath,
} from './lib/google-drive.js';
import { parseUploadedMarksheet } from './lib/reportParser.js';
import { createSendReceipt, deleteSendReceipt, getSendReceipt } from './lib/sendReceipts.js';
import { allowedTabsForRole, defaultTabForRole, isAdminPortalRole } from './lib/roles.js';

const app = new Hono();
const SERVER_CONSOLE_MAX_LINES = 600;
const SERVER_CONSOLE_DEFAULT_VIEW_LINES = 30;
const serverConsoleLines: string[] = [];
const COUNSELOR_DASHBOARD_PENDING_NOTICE_LIMIT = 5;
const OTP_EXPIRY_MS = 5 * 60 * 1000;
const OTP_RESEND_THROTTLE_MS = 30 * 1000;
const CLIENT_PUBLIC_ASSETS_ROOT = resolve(SERVER_ROOT, '..', 'client', 'public', 'assets');
const CLIENT_DIST_ROOT = resolve(SERVER_ROOT, '..', 'client', 'dist');
const TEMPLATE_FILE_MAP = {
  'counsellor-list': {
    fileName: 'counsellor_list.xlsx',
    title: 'Counsellor List',
    description: 'Reference template for counselor allocation and onboarding details.',
    icon: 'fa-user-tie',
  },
  'mark-list': {
    fileName: 'mark_list.xlsx',
    title: 'Mark List',
    description: 'Upload-ready spreadsheet for test marks, GPA, and failed subject data.',
    icon: 'fa-table-list',
  },
  'student-list': {
    fileName: 'student_list.xlsx',
    title: 'Student List',
    description: 'Base import sheet for counselor student roster management.',
    icon: 'fa-users',
  },
} as const;
const FOOTER_CREDITS_INLINE_CSS = `
  :root {
    --bg: #f6f8ff;
    --panel: #ffffff;
    --panel-soft: #f7f9ff;
    --border: #d8e2ff;
    --border-soft: #e6ecff;
    --text: #1f2a44;
    --text-dim: #5b6786;
    --text-muted: #7b87a6;
    --accent: #667eea;
    --accent-2: #764ba2;
    --shadow: 0 18px 44px rgba(31, 42, 68, .12);
  }
  * { box-sizing: border-box; }
  body {
    margin: 0;
    padding: 28px 18px 40px;
    font-family: "Inter", system-ui, -apple-system, sans-serif;
    color: var(--text);
    background:
      radial-gradient(circle at top left, rgba(102,126,234,.18), transparent 32%),
      radial-gradient(circle at bottom right, rgba(118,75,162,.14), transparent 30%),
      var(--bg);
  }
  .credits-page,
  .credits-page * {
    font-family: inherit;
  }
  .credits-page { width: min(1240px, 100%); margin: 0 auto; }
  .credits-page-hero {
    display: flex;
    justify-content: space-between;
    align-items: flex-start;
    gap: 16px;
    margin-bottom: 18px;
  }
  .credits-page-kicker {
    margin: 0 0 6px;
    text-transform: uppercase;
    letter-spacing: .11em;
    font-size: .72rem;
    color: var(--text-dim);
  }
  .credits-page-title {
    margin: 0 0 8px;
    font-size: clamp(1.4rem, 2vw, 2.1rem);
    line-height: 1.16;
  }
  .credits-page-subtitle {
    margin: 0;
    max-width: 760px;
    font-size: .92rem;
    color: var(--text-dim);
  }
  .credits-back-btn {
    display: inline-flex;
    align-items: center;
    appearance: none;
    border: 1px solid var(--border);
    background: var(--panel);
    color: var(--text);
    border-radius: 12px;
    padding: 10px 16px;
    font-weight: 700;
    cursor: pointer;
    box-shadow: 0 8px 18px rgba(31, 42, 68, .08);
    text-decoration: none;
  }
  .credits-back-btn:hover { border-color: var(--accent); }
  .credits-page-body {
    background: var(--panel);
    border: 1px solid var(--border);
    border-radius: 18px;
    box-shadow: var(--shadow);
    overflow: hidden;
  }
  .credits-compiled-shell { padding: 22px; }
  .credits-compiled-header {
    border-bottom: 1px solid var(--border);
    margin-bottom: 14px;
    padding-bottom: 12px;
  }
  .credits-compiled-title {
    margin: 0 0 4px;
    font-size: clamp(1.1rem, 1.7vw, 1.5rem);
    color: var(--text);
  }
  .credits-compiled-subtitle,
  .credits-compiled-generated {
    margin: 0;
    color: var(--text-dim);
    font-size: .82rem;
  }
  .credits-compiled-generated { margin-top: 4px; }
  .credits-columns {
    display: grid;
    grid-template-columns: repeat(2, minmax(0, 1fr));
    gap: 14px;
  }
  .credits-column {
    background: var(--panel-soft);
    border: 1px solid var(--border-soft);
    border-radius: 14px;
    padding: 12px;
  }
  .credits-column-title {
    margin-bottom: 8px;
    text-transform: uppercase;
    letter-spacing: .06em;
    font-size: .9rem;
    font-weight: 800;
  }
  .credits-column-empty {
    color: var(--text-dim);
    font-size: .84rem;
  }
  .credits-section-title {
    margin: 12px 0 8px;
    font-size: .77rem;
    letter-spacing: .08em;
    text-transform: uppercase;
    color: var(--text-muted);
  }
  .credits-person-card {
    border: 1px solid var(--border-soft);
    border-radius: 12px;
    padding: 10px;
    background: #fff;
    margin-bottom: 8px;
  }
  .credits-person-name {
    margin: 0 0 4px;
    font-size: .95rem;
    color: var(--text);
  }
  .credits-person-meta {
    margin: 0 0 8px;
    color: var(--text-dim);
    font-size: .8rem;
    line-height: 1.4;
  }
  .credits-person-list {
    margin: 0 0 0 18px;
    padding: 0;
    color: var(--text);
    display: grid;
    gap: 3px;
    font-size: .82rem;
    line-height: 1.42;
  }
  .credits-compiled-fallback {
    max-height: 62vh;
    overflow: auto;
    margin: 0;
    padding: 12px;
    border-radius: 12px;
    border: 1px solid var(--border);
    background: var(--panel-soft);
    color: var(--text);
    white-space: pre-wrap;
    font: 500 .84rem/1.5 "JetBrains Mono", Consolas, monospace;
  }
  .template-grid {
    display: grid;
    grid-template-columns: repeat(3, minmax(0, 1fr));
    gap: 14px;
    padding: 22px;
  }
  .template-card {
    background: var(--panel-soft);
    border: 1px solid var(--border-soft);
    border-radius: 16px;
    padding: 18px;
    display: grid;
    gap: 14px;
  }
  .template-card-title {
    margin: 0;
    font-size: 1.05rem;
    color: var(--text);
  }
  .template-card-copy {
    margin: 0;
    color: var(--text-dim);
    font-size: .88rem;
    line-height: 1.55;
  }
  .template-pill {
    display: inline-flex;
    align-items: center;
    width: fit-content;
    padding: 7px 11px;
    border-radius: 999px;
    border: 1px solid var(--border);
    background: rgba(102, 126, 234, .08);
    color: var(--accent);
    font-weight: 700;
    font-size: .74rem;
    letter-spacing: .05em;
    text-transform: uppercase;
  }
  .template-download-btn {
    appearance: none;
    display: inline-flex;
    align-items: center;
    justify-content: center;
    gap: 8px;
    min-height: 44px;
    border: none;
    border-radius: 12px;
    padding: 0 16px;
    background: linear-gradient(135deg, var(--accent), var(--accent-2));
    color: #fff;
    font-size: .92rem;
    font-weight: 800;
    text-decoration: none;
    box-shadow: 0 12px 24px rgba(102, 126, 234, .22);
  }
  .template-download-btn:hover {
    filter: brightness(1.02);
    transform: translateY(-1px);
  }
  @media (max-width: 980px) {
    body { padding: 18px 12px 28px; }
    .credits-page-hero { flex-direction: column; }
    .credits-columns { grid-template-columns: 1fr; }
    .template-grid { grid-template-columns: 1fr; }
  }
`;

type PendingLoginOtpChallenge = {
  email: string;
  role: string;
  forceLogoutOthers: boolean;
  otpHash: string;
  expiresAt: number;
  requestedAt: number;
  invalidAttempts: number;
};

type PendingPasswordResetChallenge = {
  email: string;
  role: string;
  otpHash: string;
  expiresAt: number;
  requestedAt: number;
  verifiedAt: number | null;
};

type PendingSelfResetOtpChallenge = {
  email: string;
  otpHash: string;
  expiresAt: number;
  requestedAt: number;
};

const pendingLoginOtpChallenges = new Map<string, PendingLoginOtpChallenge>();
const pendingPasswordResetChallenges = new Map<string, PendingPasswordResetChallenge>();
const pendingSelfResetOtpChallenges = new Map<string, PendingSelfResetOtpChallenge>();

function nowMs() {
  return Date.now();
}

function hashOtp(value: string) {
  return createHash('sha256').update(String(value || '')).digest('hex');
}

function generateOtpCode() {
  return String(Math.floor(100000 + Math.random() * 900000));
}

function maskEmailAddress(email: string) {
  const normalized = String(email || '').trim();
  if (!normalized.includes('@')) return normalized;
  const [local, domain] = normalized.split('@');
  const first = local.slice(0, 1);
  const last = local.length > 1 ? local.slice(-1) : '';
  const hidden = '*'.repeat(Math.max(1, local.length - (first ? 1 : 0) - (last ? 1 : 0)));
  return `${first}${hidden}${last}@${domain}`;
}

function cleanupExpiredChallengeMap<T extends { expiresAt: number }>(store: Map<string, T>) {
  const current = nowMs();
  for (const [token, value] of store.entries()) {
    if (Number(value.expiresAt || 0) <= current) {
      store.delete(token);
    }
  }
}

function isOtpCookieFresh(payload: { expiresAt: number } | null | undefined) {
  return !!payload && Number(payload.expiresAt || 0) > nowMs();
}

function getBooleanConfigValue(value: unknown) {
  return String(value || 'false').trim().toLowerCase() === 'true';
}

function isLoginOtpRequiredForUser(userRow: Record<string, unknown>, appConfig: Record<string, string>) {
  if (!getBooleanConfigValue(appConfig.require_otp_on_login)) return false;

  const role = String(userRow.role || '').trim().toLowerCase();
  if (role === 'counselor' && !getBooleanConfigValue(appConfig.counselor_login_otp_enabled)) {
    return false;
  }

  return true;
}

function getAuthUiConfig(authUser: ReturnType<typeof toAuthUser> | null, appConfig: Record<string, string>) {
  const smtpReady = getSmtpStatus().state === 'ready';
  const googleOauthEnabled = getGoogleOauthSettings(appConfig).enabled;
  return {
    smtpReady,
    googleOauthEnabled,
    standardOtpLoginEnabled: getBooleanConfigValue(appConfig.require_otp_on_login),
    forgotPasswordEnabled: smtpReady,
    selfPasswordOtpEnabled: smtpReady && getBooleanConfigValue(appConfig.require_otp_on_password_reset),
    adminCurrentPasswordFallbackEnabled: !getBooleanConfigValue(appConfig.require_otp_on_password_reset) && authUser?.role === 'admin',
  };
}

function sanitizeAppConfigForClient(appConfig: Record<string, string>, authUser: ReturnType<typeof toAuthUser> | null) {
  return {
    ...appConfig,
    smtp_password: '',
    google_oauth_client_secret: '',
    google_oauth_bulk_override_password: '',
    google_drive_refresh_token: '',
  };
}

async function sendOtpEmail(targetEmail: string, purpose: string, otpCode: string) {
  const config = getAppConfig();
  const status = getSmtpStatus();
  if (status.state !== 'ready') return false;

  try {
    const transporter = nodemailer.createTransport({
      host: String(config.smtp_server || '').trim(),
      port: Number(String(config.smtp_port || '587').trim() || 587),
      secure: Number(String(config.smtp_port || '587').trim() || 587) === 465,
      auth: {
        user: String(config.smtp_username || '').trim(),
        pass: String(config.smtp_password || ''),
      },
    });

    const expiresMinutes = Math.max(1, Math.round(OTP_EXPIRY_MS / 60000));
    await transporter.sendMail({
      from: String(config.email_from || 'RMKCET Parent Connect <noreply@rmkcet.ac.in>').trim(),
      to: targetEmail,
      subject: `${APP_NAME} - ${purpose} OTP`,
      text: `Your ${purpose} OTP is ${otpCode}. This OTP is valid for ${expiresMinutes} minutes.`,
      html: `<div style="font-family:Arial,sans-serif;line-height:1.6;color:#0f172a;">
        <h2 style="margin-bottom:8px;">${APP_NAME}</h2>
        <p>Your <strong>${purpose}</strong> OTP is:</p>
        <div style="font-size:28px;font-weight:800;letter-spacing:6px;color:#2563eb;margin:16px 0;">${otpCode}</div>
        <p>This OTP is valid for ${expiresMinutes} minutes.</p>
      </div>`,
    });
    return true;
  } catch (error) {
    appendServerConsoleLine(`OTP email failed for ${targetEmail}: ${error instanceof Error ? error.message : 'Unknown error'}`);
    return false;
  }
}

function setChallengeCookie(c: Context, cookieName: string, token: string, maxAgeMs = OTP_EXPIRY_MS) {
  setCookie(c, cookieName, token, {
    path: '/',
    httpOnly: true,
    sameSite: 'Lax',
    maxAge: Math.max(60, Math.ceil(maxAgeMs / 1000)),
  });
}

function clearChallengeCookie(c: Context, cookieName: string) {
  deleteCookie(c, cookieName, { path: '/' });
}

async function createLoginOtpChallenge(c: Context, userRow: Record<string, unknown>, forceLogoutOthers: boolean) {
  cleanupExpiredChallengeMap(pendingLoginOtpChallenges);
  const email = String(userRow.email || '').trim().toLowerCase();
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(email, 'Login', otpCode);
  if (!sent) return null;
  const token = randomUUID();
  pendingLoginOtpChallenges.set(token, {
    email,
    role: String(userRow.role || '').trim().toLowerCase(),
    forceLogoutOthers,
    otpHash: hashOtp(otpCode),
    expiresAt: nowMs() + OTP_EXPIRY_MS,
    requestedAt: nowMs(),
    invalidAttempts: 0,
  });
  setChallengeCookie(c, LOGIN_OTP_COOKIE, token);
  return { maskedEmail: maskEmailAddress(email) };
}

async function refreshLoginOtpChallenge(c: Context, token: string, challenge: PendingLoginOtpChallenge) {
  if (nowMs() - Number(challenge.requestedAt || 0) < OTP_RESEND_THROTTLE_MS) {
    throw new Error('Please wait 30 seconds before requesting another OTP.');
  }
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(challenge.email, 'Login', otpCode);
  if (!sent) throw new Error('Unable to resend OTP right now. Please try again.');
  pendingLoginOtpChallenges.set(token, {
    ...challenge,
    otpHash: hashOtp(otpCode),
    expiresAt: nowMs() + OTP_EXPIRY_MS,
    requestedAt: nowMs(),
  });
  return { maskedEmail: maskEmailAddress(challenge.email) };
}

async function createPasswordResetChallenge(c: Context, userRow: Record<string, unknown>) {
  cleanupExpiredChallengeMap(pendingPasswordResetChallenges);
  const email = String(userRow.email || '').trim().toLowerCase();
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(email, 'Password Reset', otpCode);
  if (!sent) return null;
  const token = randomUUID();
  pendingPasswordResetChallenges.set(token, {
    email,
    role: String(userRow.role || '').trim().toLowerCase(),
    otpHash: hashOtp(otpCode),
    expiresAt: nowMs() + OTP_EXPIRY_MS,
    requestedAt: nowMs(),
    verifiedAt: null,
  });
  setChallengeCookie(c, PASSWORD_RESET_COOKIE, token);
  return { maskedEmail: maskEmailAddress(email) };
}

async function createSelfResetOtpChallenge(c: Context, authUser: ReturnType<typeof toAuthUser>) {
  cleanupExpiredChallengeMap(pendingSelfResetOtpChallenges);
  const existingToken = getCookie(c, SELF_RESET_OTP_COOKIE) || '';
  const existing = existingToken ? pendingSelfResetOtpChallenges.get(existingToken) : null;
  if (existing && nowMs() - Number(existing.requestedAt || 0) < OTP_RESEND_THROTTLE_MS) {
    throw new Error('Please wait 30 seconds before requesting another OTP.');
  }
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(authUser.email, 'Password Reset', otpCode);
  if (!sent) throw new Error('Unable to send OTP. Check SMTP configuration and try again.');
  const token = existingToken || randomUUID();
  pendingSelfResetOtpChallenges.set(token, {
    email: authUser.email,
    otpHash: hashOtp(otpCode),
    expiresAt: nowMs() + OTP_EXPIRY_MS,
    requestedAt: nowMs(),
  });
  setChallengeCookie(c, SELF_RESET_OTP_COOKIE, token);
  return { maskedEmail: maskEmailAddress(authUser.email) };
}

function parseDashboardMark(value: unknown) {
  const raw = String(value ?? '').trim();
  if (!raw) return null;
  const upper = raw.toUpperCase();
  if (['ABSENT', 'AB', 'A', '-', 'NA', 'N/A'].includes(upper)) return null;
  const numeric = Number(raw);
  if (!Number.isFinite(numeric) || numeric < 0 || numeric > 100) return null;
  return numeric;
}

function isDashboardAttendanceField(name: unknown) {
  const normalized = String(name ?? '').trim().toLowerCase().replace(/[^a-z0-9]/g, '');
  return [
    'attendance',
    'att',
    'attendence',
    'absentees',
    'absentee',
    'absentstudents',
    'absentcount',
    'examnotattended',
    'notattended',
    'noofsubjectsabsent',
    'gpa',
    'cgpa',
    'noofsubjectsfailed',
    'failedsubjects',
    'failedcount',
    'nooffailedsubjects',
    'total',
    'overall',
    'percentage',
    'grade',
    'result',
    'status',
  ].includes(normalized);
}

function isDashboardFailedField(name: unknown) {
  const normalized = String(name ?? '').trim().toLowerCase().replace(/[^a-z0-9]/g, '');
  return [
    'noofsubjectsfailed',
    'failedsubjects',
    'failedcount',
    'nooffailedsubjects',
  ].includes(normalized);
}

function getCounselorDashboardStudentInsights(counselorEmail: string) {
  const rows = db
    .prepare(
      `
        SELECT
          cs.reg_no,
          cs.student_name,
          sm.subject_name,
          COALESCE(cmo.marks, sm.marks) AS marks
        FROM counselor_students cs
        JOIN users u ON u.email = cs.counselor_email
        JOIN student_marks sm
          ON REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '')
        JOIN test_metadata tm ON tm.test_id = sm.test_id
        LEFT JOIN counselor_mark_overrides cmo
          ON cmo.counselor_email = cs.counselor_email
         AND cmo.test_id = sm.test_id
         AND REPLACE(UPPER(TRIM(cmo.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
         AND cmo.subject_name = sm.subject_name
        WHERE LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(?))
          AND UPPER(COALESCE(tm.department, '')) = UPPER(COALESCE(u.department, ''))
          AND CAST(COALESCE(tm.year_level, 1) AS INTEGER) = CAST(COALESCE(u.year_level, 1) AS INTEGER)
          AND COALESCE(cs.is_active, 1) = 1
      `,
    )
    .all(counselorEmail) as Array<{
    reg_no: string;
    student_name: string;
    subject_name: string;
    marks: string;
  }>;

  const students = new Map<
    string,
    {
      reg_no: string;
      name: string;
      sum: number;
      count: number;
      failedSum: number;
      failedCount: number;
      subjectMarks: Map<string, { sum: number; count: number }>;
    }
  >();

  for (const item of rows) {
    const regNo = String(item.reg_no || '').trim();
    if (!regNo) continue;

    const subjectName = String(item.subject_name || '').trim() || 'Subject';
    const current =
      students.get(regNo)
      || {
        reg_no: regNo,
        name: String(item.student_name || regNo).trim() || regNo,
        sum: 0,
        count: 0,
        failedSum: 0,
        failedCount: 0,
        subjectMarks: new Map<string, { sum: number; count: number }>(),
      };

    if (isDashboardFailedField(subjectName)) {
      const failedValue = parseDashboardMark(item.marks);
      if (failedValue !== null) {
        current.failedSum += failedValue;
        current.failedCount += 1;
        students.set(regNo, current);
      }
      continue;
    }

    if (isDashboardAttendanceField(subjectName)) continue;

    const mark = parseDashboardMark(item.marks);
    if (mark === null) continue;

    current.sum += mark;
    current.count += 1;

    const subjectBucket = current.subjectMarks.get(subjectName) || { sum: 0, count: 0 };
    subjectBucket.sum += mark;
    subjectBucket.count += 1;
    current.subjectMarks.set(subjectName, subjectBucket);
    students.set(regNo, current);
  }

  const rankedStudents = [...students.values()]
    .filter((student) => student.count > 0)
    .map((student) => {
      const averageMarks = student.sum / Math.max(1, student.count);
      return {
        reg_no: student.reg_no,
        name: student.name,
        average_marks: Math.round(averageMarks * 10) / 10,
        gpa: Math.round(Math.max(0, Math.min(10, averageMarks / 10)) * 100) / 100,
        failed_subjects: student.failedCount > 0 ? Math.round(student.failedSum / Math.max(1, student.failedCount)) : null,
        subject_marks: [...student.subjectMarks.entries()]
          .sort((a, b) => a[0].localeCompare(b[0]))
          .map(([subject, bucket]) => ({
            subject,
            marks: Math.round((bucket.sum / Math.max(1, bucket.count)) * 10) / 10,
          })),
      };
    });

  const byBest = [...rankedStudents].sort((a, b) => {
    if (b.gpa !== a.gpa) return b.gpa - a.gpa;
    return a.name.localeCompare(b.name);
  });

  const byNeedsHelp = [...rankedStudents].sort((a, b) => {
    if (a.gpa !== b.gpa) return a.gpa - b.gpa;
    return a.name.localeCompare(b.name);
  });

  return {
    topPerformingStudents: byBest.slice(0, 3),
    studentsNeedImprovement: byNeedsHelp.slice(0, 3),
  };
}

function buildCounselorOverviewPayload(counselorEmail: string) {
  const recentTests = getVisibleTestsForCounselor(counselorEmail);
  const pendingNotices = getVisibleNoticesForCounselor(counselorEmail, { filterStatus: 'pending' }).slice(0, COUNSELOR_DASHBOARD_PENDING_NOTICE_LIMIT);
  const insights = getCounselorDashboardStudentInsights(counselorEmail);

  return {
    studentCount: getStudentCountForCounselor(counselorEmail),
    testCount: recentTests.length,
    messageStats: getCounselorMessageStats(counselorEmail),
    recentTests: recentTests.slice(0, 2),
    pendingNotices,
    ...insights,
  };
}

function appendServerConsoleLine(message: string) {
  const text = String(message || '').trim();
  if (!text) return;
  const timestamp = new Date().toISOString().slice(0, 19).replace('T', ' ');
  serverConsoleLines.push(`[${timestamp}] ${text}`);
  if (serverConsoleLines.length > SERVER_CONSOLE_MAX_LINES) {
    serverConsoleLines.splice(0, serverConsoleLines.length - SERVER_CONSOLE_MAX_LINES);
  }
}

function getServerConsoleLines(limit = SERVER_CONSOLE_DEFAULT_VIEW_LINES) {
  const safeLimit = Math.max(1, Math.min(200, Number(limit || SERVER_CONSOLE_DEFAULT_VIEW_LINES) || SERVER_CONSOLE_DEFAULT_VIEW_LINES));
  return serverConsoleLines.slice(-safeLimit);
}

function parseScopeValue(rawValue: string) {
  const [departmentRaw, yearRaw] = String(rawValue || '').split('::');
  const department = String(departmentRaw || '').trim().toUpperCase();
  const yearLevel = Number(yearRaw || 0);
  if (!department || ![1, 2, 3, 4].includes(yearLevel)) return null;
  return { department, year_level: yearLevel };
}

function parseScopeValues(values: unknown[]) {
  const scopes: Array<{ department: string; year_level: number }> = [];
  const seen = new Set<string>();
  for (const value of values || []) {
    const scope = parseScopeValue(String(value || ''));
    if (!scope) continue;
    const key = `${scope.department}::${scope.year_level}`;
    if (seen.has(key)) continue;
    seen.add(key);
    scopes.push(scope);
  }
  return scopes;
}

function normalizeUserRole(rawRole: string) {
  const role = String(rawRole || '').trim().toLowerCase();
  if (role === 'hod') return 'hod';
  if (role === 'deo') return 'deo';
  if (role === 'principal') return 'principal';
  if (role === 'admin') return 'admin';
  return 'counselor';
}

function actorCanManageUser(actor: ReturnType<typeof toAuthUser>, target: Record<string, unknown> | null, mode: 'edit' | 'manage') {
  if (!target) return false;
  const targetRole = normalizeUserRole(String(target.role || 'counselor'));
  const targetEmail = String(target.email || '').trim().toLowerCase();
  if (actor.role === 'principal') return false;
  if (actor.role === 'admin') {
    if (mode === 'manage' && targetEmail === actor.email && targetRole === 'admin') return false;
    return true;
  }
  if (actor.role === 'deo') {
    if (targetRole !== 'counselor') return false;
    const allowed = new Set(actor.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
    return allowed.has(`${String(target.department || '').trim().toUpperCase()}::${Number(target.year_level || 1)}`);
  }
  return false;
}

function getAssignableRolesForActor(role: string) {
  if (role === 'admin') return ['counselor', 'hod', 'deo', 'principal', 'admin'];
  if (role === 'deo') return ['counselor'];
  return [];
}

function mapUserForClient(actor: ReturnType<typeof toAuthUser>, item: ReturnType<typeof listUsersForActor>[number]) {
  return {
    ...item,
    can_edit: actorCanManageUser(actor, item as unknown as Record<string, unknown>, 'edit'),
    can_manage: actorCanManageUser(actor, item as unknown as Record<string, unknown>, 'manage'),
  };
}

function parseBulkCounselorWorkbook(buffer: Buffer, departmentCodes: string[]) {
  const workbook = XLSX.read(buffer, { type: 'buffer' });
  const validDepartments = new Set((departmentCodes || []).map((code) => String(code || '').trim().toUpperCase()));
  const parsedRows: Array<{
    name: string;
    email: string;
    department: string;
    password: string;
    needs_lock: boolean;
    missing_required: string[];
  }> = [];

  for (const sheetName of workbook.SheetNames) {
    const sheet = workbook.Sheets[sheetName];
    if (!sheet) continue;
    const rows = XLSX.utils.sheet_to_json<Record<string, unknown>>(sheet, { defval: '' });
    for (const row of rows) {
      const entries = Object.entries(row || {});
      const normalized = new Map(entries.map(([key, value]) => [String(key || '').trim().toLowerCase().replace(/[^a-z0-9]/g, ''), String(value || '').trim()]));
      const getFirst = (...candidates: string[]) => {
        for (const candidate of candidates) {
          for (const [key, value] of normalized.entries()) {
            if (key === candidate || key.includes(candidate)) return value;
          }
        }
        return '';
      };

      const name = getFirst('name', 'counselorname');
      const email = getFirst('email', 'mailid').toLowerCase();
      const departmentRaw = getFirst('branch', 'department');
      const password = getFirst('password');

      let department = '';
      const departmentToken = String(departmentRaw || '').trim().toUpperCase();
      if (departmentToken) {
        if (validDepartments.has(departmentToken)) {
          department = departmentToken;
        } else {
          const matched = Array.from(validDepartments).find((code) => departmentToken.includes(code) || code.includes(departmentToken));
          if (matched) department = matched;
        }
      }

      if (!email || !email.includes('@')) continue;
      const missingRequired: string[] = [];
      if (!name) missingRequired.push('name');
      if (!department) missingRequired.push('department');
      if (!password) missingRequired.push('password');

      parsedRows.push({
        name,
        email,
        department,
        password,
        needs_lock: missingRequired.length > 0,
        missing_required: missingRequired,
      });
    }
  }

  const seen = new Set<string>();
  return parsedRows.filter((row) => {
    if (seen.has(row.email)) return false;
    seen.add(row.email);
    return true;
  });
}

function parseStudentWorkbook(buffer: Buffer) {
  const workbook = XLSX.read(buffer, { type: 'buffer' });
  const students: Array<{ reg_no: string; student_name: string; department?: string; parent_phone?: string; parent_email?: string }> = [];

  for (const sheetName of workbook.SheetNames) {
    const sheet = workbook.Sheets[sheetName];
    if (!sheet) continue;
    const rows = XLSX.utils.sheet_to_json<Record<string, unknown>>(sheet, { defval: '' });
    for (const row of rows) {
      const normalized = new Map(
        Object.entries(row || {}).map(([key, value]) => [String(key || '').trim().toLowerCase().replace(/[^a-z0-9]/g, ''), String(value || '').trim()]),
      );
      const pick = (...candidates: string[]) => {
        for (const candidate of candidates) {
          for (const [key, value] of normalized.entries()) {
            if (key === candidate || key.includes(candidate)) return value;
          }
        }
        return '';
      };

      const regNo = pick('rno', 'regno', 'rollno', 'registernumber');
      const studentName = pick('name', 'studentname');
      const parentPhone = pick('wno', 'whatsappno', 'parentphone', 'phone');
      const parentEmail = pick('parentemail', 'email');
      const department = pick('department', 'branch');
      if (!regNo || !studentName) continue;
      students.push({
        reg_no: regNo,
        student_name: studentName,
        parent_phone: parentPhone,
        parent_email: parentEmail,
        department: String(department || '').trim().toUpperCase(),
      });
    }
  }
  return students;
}

function sessionCookieMaxAge(appConfig: Record<string, string>) {
  const timeoutSeconds = Number(appConfig.session_timeout || 86400);
  return Number.isFinite(timeoutSeconds) && timeoutSeconds > 300 ? timeoutSeconds : 86400;
}

function canManageDepartmentYear(
  authUser: { role: string; scopes: Array<{ department: string; year_level: number }> } | null,
  department: string,
  yearLevel: number,
) {
  if (!authUser) return false;
  if (authUser.role === 'admin' || authUser.role === 'principal') return true;
  if (authUser.role !== 'hod' && authUser.role !== 'deo') return false;
  const key = `${String(department || '').trim().toUpperCase()}::${Number(yearLevel || 1)}`;
  return authUser.scopes.some((scope) => `${scope.department.toUpperCase()}::${scope.year_level}` === key);
}

function normalizeRegNo(value: string) {
  let reg = String(value || '').trim().replace(/\s+/g, '');
  if (reg.endsWith('.0')) reg = reg.slice(0, -2);
  return reg.toUpperCase();
}

function normalizePhone(value: string) {
  const digits = String(value || '').replace(/\D/g, '');
  return digits.length >= 10 ? digits.slice(-10) : '';
}

function parseNoticeScopeValues(values: FormDataEntryValue[]) {
  return values
    .map((value) => String(value || '').trim())
    .map((value) => {
      const [department, yearValue] = value.split('::');
      return {
        department: String(department || '').trim().toUpperCase(),
        year_level: Number(yearValue || 0) || 0,
      };
    })
    .filter((item) => item.department && [1, 2, 3, 4].includes(item.year_level));
}

function sanitizeFileName(name: string) {
  return String(name || 'file')
    .replace(/[^\w.\-() ]+/g, '_')
    .replace(/\s+/g, ' ')
    .trim();
}

function stripProtocol(url: string) {
  return String(url || '').trim().replace(/^https?:\/\//i, '');
}

function buildNoticeAttachmentLink(c: Context, publicToken: string) {
  const token = String(publicToken || '').trim();
  if (!token) return '';
  return `${new URL(c.req.url).origin}/notice-files/${token}`;
}

function buildNoticeAttachmentLinksText(
  c: Context,
  attachments: Array<{ public_token?: string }>,
) {
  return attachments
    .map((attachment) => buildNoticeAttachmentLink(c, String(attachment.public_token || '')))
    .filter(Boolean)
    .map((url) => stripProtocol(url))
    .join('\n');
}

function buildDefaultNoticeMessage(noticeTitle = '', noticeText = '', attachmentLinks = '') {
  const title = String(noticeTitle || '').trim() || 'Notice';
  const text = String(noticeText || '').trim();
  const links = String(attachmentLinks || '').trim();

  let message = `Dear Parent , \nSub : ${title} \n\n${text}`.trim();
  if (links) {
    message = `${message}\n\nAttachments:\n${links}`.trim();
  }
  return message;
}

function appendNoticeAttachmentBlock(message: string, attachmentLinks: string) {
  const baseMessage = String(message || '').trim();
  const links = String(attachmentLinks || '').trim();
  if (!links) return baseMessage;
  if (baseMessage.includes(links) || baseMessage.includes('Attachments:')) return baseMessage;
  if (baseMessage) return `${baseMessage}\n\nAttachments:\n${links}`.trim();
  return `Attachments:\n${links}`.trim();
}

function canFullyManageNotice(authUser: { role: string; scopes: Array<{ department: string; year_level: number }> }, noticeId: number) {
  if (authUser.role === 'admin' || authUser.role === 'principal') return true;
  if (authUser.role !== 'hod' && authUser.role !== 'deo') return false;
  const notice = getNotice(noticeId);
  if (!notice || Boolean(Number(notice.send_to_all || 0))) return false;
  const scopes = getNoticeScopePairs(noticeId);
  if (!scopes.length) return false;
  const allowed = new Set(authUser.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
  return scopes.every((scope) => allowed.has(`${scope.department}::${scope.year_level}`));
}

const AUTO_BACKUP_FILE_PREFIX = 'rmkcet_shine_auto_';
const LEGACY_AUTO_BACKUP_FILE_PREFIX = 'auto_backup_';
const BACKUP_SNAPSHOT_SUFFIX = '.snapshot';

type PreservedSessionRow = {
  session_id: string;
  user_email: string;
  login_time: string;
  last_activity: string;
  ip_address: string;
  user_agent: string;
  browser_info: string;
  tab_id: string;
  is_active: number;
  forced_logout: number;
  logout_reason: string | null;
};

function isAutomaticBackupFileName(fileName: string) {
  const normalized = String(fileName || '').trim().toLowerCase();
  return normalized.startsWith(AUTO_BACKUP_FILE_PREFIX) || normalized.startsWith(LEGACY_AUTO_BACKUP_FILE_PREFIX);
}

function getBackupSnapshotDir(backupPath: string) {
  return `${backupPath}${BACKUP_SNAPSHOT_SUFFIX}`;
}

function isSystemAdmin(role: string) {
  return String(role || '').trim().toLowerCase() === 'admin';
}

function isPrincipal(role: string) {
  return String(role || '').trim().toLowerCase() === 'principal';
}

function enforceDefaultAdminDisablePolicy() {
  const config = getAppConfig();
  if (String(config.disable_default_admin_on_new_system_admin || 'false').toLowerCase() !== 'true') return false;

  const defaultAdminEmail = String(DEFAULT_SYSTEM_ADMIN_EMAIL || '').trim().toLowerCase();
  if (!defaultAdminEmail) return false;

  const otherAdminCountRow = db.prepare(
    `
      SELECT COUNT(*) AS count
      FROM users
      WHERE LOWER(COALESCE(role, '')) = 'admin'
        AND LOWER(COALESCE(email, '')) <> ?
    `,
  ).get(defaultAdminEmail) as { count?: number } | undefined;

  const hasOtherSystemAdmin = Number(
    otherAdminCountRow?.count || 0,
  ) > 0;
  if (!hasOtherSystemAdmin) return false;

  const defaultAdmin = getUserByEmail(defaultAdminEmail);
  if (!defaultAdmin) return false;
  if (!Number(defaultAdmin.is_active || 0) && Number(defaultAdmin.is_locked || 0)) return false;

  lockUser(defaultAdminEmail, 'Disabled automatically after another system admin was created');
  return true;
}

function capturePrivilegedSessions() {
  return db.prepare(
    `
      SELECT s.session_id, s.user_email, s.login_time, s.last_activity, s.ip_address, s.user_agent,
             s.browser_info, s.tab_id, s.is_active, s.forced_logout, s.logout_reason
      FROM active_sessions s
      INNER JOIN users u ON u.email = s.user_email
      WHERE s.is_active = 1
        AND LOWER(COALESCE(u.role, '')) IN ('admin', 'principal')
    `,
  ).all() as PreservedSessionRow[];
}

function restorePrivilegedSessions(rows: PreservedSessionRow[]) {
  if (!rows.length) return;
  const insertSession = db.prepare(`
    INSERT OR REPLACE INTO active_sessions (
      session_id, user_email, login_time, last_activity, ip_address, user_agent, browser_info, tab_id, is_active, forced_logout, logout_reason
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
  `);
  const updateUserSession = db.prepare(`
    UPDATE users
    SET session_id = ?, last_login = COALESCE(last_login, ?), last_activity = ?
    WHERE email = ?
      AND LOWER(COALESCE(role, '')) IN ('admin', 'principal')
      AND COALESCE(is_active, 0) = 1
      AND COALESCE(is_locked, 0) = 0
  `);
  const transaction = db.transaction((sessionRows: PreservedSessionRow[]) => {
    for (const item of sessionRows) {
      const user = getUserByEmail(String(item.user_email || '').trim().toLowerCase());
      if (!user) continue;
      const role = String(user.role || '').trim().toLowerCase();
      if (role !== 'admin' && role !== 'principal') continue;
      if (!Number(user.is_active || 0) || Number(user.is_locked || 0)) continue;
      insertSession.run(
        item.session_id,
        item.user_email,
        item.login_time,
        item.last_activity,
        item.ip_address || '',
        item.user_agent || '',
        item.browser_info || '',
        item.tab_id || '',
        1,
        0,
        null,
      );
      updateUserSession.run(item.session_id, item.login_time, item.last_activity, item.user_email);
    }
  });
  transaction(rows);
}

function canAccessAdminMessages(role: string) {
  return ['admin', 'hod', 'deo'].includes(String(role || '').trim().toLowerCase());
}

function getAllowedCounselorEmailsForActor(authUser: {
  email: string;
  name: string;
  role: string;
  department: string | null;
  year_level: number;
  scopes: Array<{ department: string; year_level: number }>;
}) {
  return getUsersForActor(authUser as Parameters<typeof getUsersForActor>[0])
    .filter((item) => String(item.role || '').trim().toLowerCase() === 'counselor')
    .map((item) => String(item.email || '').trim().toLowerCase());
}

function getVisibleDepartmentsForActor(authUser: { role: string; department: string | null; scopes: Array<{ department: string; year_level: number }> }) {
  const allDepartments = getDepartments(true);
  if (authUser.role === 'admin' || authUser.role === 'principal') return allDepartments;
  if (authUser.role === 'hod' || authUser.role === 'deo') {
    return allDepartments.filter((department) =>
      authUser.scopes.some((scope) => scope.department.toUpperCase() === department.code.toUpperCase()),
    );
  }
  return allDepartments.filter((department) => department.code.toUpperCase() === String(authUser.department || '').trim().toUpperCase());
}

function getScopedYearsByDepartment(authUser: { role: string; scopes: Array<{ department: string; year_level: number }> }) {
  const map = new Map<string, number[]>();
  if (authUser.role === 'admin' || authUser.role === 'principal') {
    for (const department of getDepartments(true)) {
      map.set(department.code.toUpperCase(), [1, 2, 3, 4]);
    }
    return map;
  }
  for (const scope of authUser.scopes) {
    const key = String(scope.department || '').trim().toUpperCase();
    if (!map.has(key)) map.set(key, []);
    map.get(key)!.push(Number(scope.year_level || 1));
  }
  for (const [key, values] of map.entries()) {
    map.set(key, Array.from(new Set(values)).sort((a, b) => a - b));
  }
  return map;
}

function getSmtpStatus() {
  const config = getAppConfig();
  const server = String(config.smtp_server || '').trim();
  const username = String(config.smtp_username || '').trim();
  const password = String(config.smtp_password || '').trim();
  const emailFrom = String(config.email_from || '').trim();
  const port = String(config.smtp_port || '587').trim();

  if (!server || !username || !password) {
    return {
      state: 'missing',
      label: 'SMTP Missing',
      detail: 'SMTP username/password are not configured.',
      config: { server, username, email_from: emailFrom, port },
    };
  }

  return {
    state: 'ready',
    label: 'SMTP Ready',
    detail: 'SMTP credentials are configured.',
    config: { server, username, email_from: emailFrom, port },
  };
}

function getLatestBackupEntry(
  entries: Array<{ name: string; modified: string; size_kb: number }>,
) {
  return [...entries].sort((a, b) => Date.parse(String(b.modified || '').replace(' ', 'T')) - Date.parse(String(a.modified || '').replace(' ', 'T')))[0] || null;
}

async function getAdminDashboardStatus() {
  const appConfig = getAppConfig();
  const smtp = getSmtpStatus();
  const oauth = getGoogleOauthSettings(appConfig);
  const sessionStats = getSessionStatistics();
  const storageMode = getBackupStorageMode(appConfig);
  const driveSettings = getGoogleDriveSettings(appConfig);

  let backupHealth: 'healthy' | 'warning' | 'error' = 'healthy';
  let backupLabel = storageMode === 'gdrive' ? 'Google Drive Connected' : 'Local Backup Storage';
  let backupDetail = storageMode === 'gdrive'
    ? 'Google Drive backup storage is active.'
    : 'Backups are stored in the local rebuild data folder.';
  let backupFiles = { autoBackupFiles: [] as Array<{ name: string; modified: string; size_kb: number }>, backupFiles: [] as Array<{ name: string; modified: string; size_kb: number }> };
  let archiveFiles: Array<{ name: string; modified: string; size_kb: number }> = [];

  try {
    backupFiles = await listBackupFiles();
    archiveFiles = await listArchiveFiles();
    const totalBackupCount = backupFiles.autoBackupFiles.length + backupFiles.backupFiles.length;
    if (storageMode === 'gdrive' && !driveSettings.enabled) {
      backupHealth = 'error';
      backupLabel = 'Google Drive Not Configured';
      backupDetail = 'Drive mode is selected, but the OAuth client or refresh token is incomplete.';
    } else if (totalBackupCount === 0) {
      backupHealth = 'warning';
      backupLabel = storageMode === 'gdrive' ? 'Google Drive Ready' : 'Local Storage Ready';
      backupDetail = 'Storage is available, but no backups have been created yet.';
    } else {
      const latest = getLatestBackupEntry([...backupFiles.autoBackupFiles, ...backupFiles.backupFiles]);
      if (latest) {
        backupDetail = `Latest backup: ${latest.name} on ${latest.modified}.`;
      }
    }
  } catch (error) {
    backupHealth = 'error';
    backupLabel = storageMode === 'gdrive' ? 'Google Drive Health Issue' : 'Local Backup Health Issue';
    backupDetail = error instanceof Error ? error.message : 'Unable to inspect backup storage.';
  }

  const latestBackup = getLatestBackupEntry([...backupFiles.autoBackupFiles, ...backupFiles.backupFiles]);
  const oauthHealthy = !String(appConfig.google_oauth_enabled || 'false').trim().toLowerCase().includes('true')
    ? false
    : oauth.enabled;

  return {
    smtp,
    oauth: {
      enabled: oauth.enabled,
      healthy: oauthHealthy,
      label: oauth.enabled ? 'Google OAuth Enabled' : 'Google OAuth Disabled',
      detail: oauth.enabled
        ? `OAuth is ready${oauth.allowedDomain ? ` for ${oauth.allowedDomain}` : ''}.`
        : 'Google sign-in is currently disabled or incomplete.',
      allowed_domain: oauth.allowedDomain,
      redirect_base_url: oauth.redirectBaseUrl,
    },
    backup: {
      storage_mode: storageMode,
      health: backupHealth,
      label: backupLabel,
      detail: backupDetail,
      drive_configured: driveSettings.enabled,
      periodic_enabled: String(appConfig.enable_periodic_backups || 'false').trim().toLowerCase() === 'true',
      backup_count: backupFiles.backupFiles.length,
      auto_backup_count: backupFiles.autoBackupFiles.length,
      archive_count: archiveFiles.length,
      latest_backup_name: latestBackup?.name || '',
      latest_backup_modified: latestBackup?.modified || '',
    },
    sessions: {
      active_sessions: sessionStats.active_sessions,
      today_sessions: sessionStats.today_sessions,
      peak_concurrent: sessionStats.peak_concurrent,
      forced_logouts: sessionStats.forced_logouts,
    },
  };
}

async function buildDashboardOverview(authUser: ReturnType<typeof toAuthUser>) {
  const departments = getVisibleDepartmentsForActor(authUser);
  const allowedScopes =
    authUser.role === 'admin' || authUser.role === 'principal'
      ? null
      : new Set(authUser.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
  const activityRows = getCounselorActivitySummary().filter((item) => {
    if (authUser.role === 'admin' || authUser.role === 'principal') return true;
    const key = `${String(item.department || '').trim().toUpperCase()}::${Number(item.year_level || 1)}`;
    return !!allowedScopes?.has(key);
  });
  const noticeRows = getNoticeCompletionRows(authUser);

  function buildCompletionOverview<T>(
    rows: T[],
    readDepartment: (row: T) => string,
    readYear: (row: T) => number,
    readCompleted: (row: T) => number,
    readTotal: (row: T) => number,
    isPending: (row: T) => boolean,
  ) {
    const buckets = new Map<string, { completed: number; total: number; years: Record<number, { completed: number; total: number }> }>();
    let completedTotal = 0;
    let grandTotal = 0;
    let pendingCounselors = 0;

    for (const row of rows) {
      const department = String(readDepartment(row) || 'N/A').trim().toUpperCase();
      const yearLevel = Number(readYear(row) || 1);
      const completed = Math.max(0, Number(readCompleted(row) || 0));
      const total = Math.max(0, Number(readTotal(row) || 0));
      if (isPending(row)) pendingCounselors += 1;

      completedTotal += completed;
      grandTotal += total;

      if (!buckets.has(department)) {
        buckets.set(department, { completed: 0, total: 0, years: {} });
      }
      const bucket = buckets.get(department)!;
      bucket.completed += completed;
      bucket.total += total;

      if (!bucket.years[yearLevel]) {
        bucket.years[yearLevel] = { completed: 0, total: 0 };
      }
      bucket.years[yearLevel].completed += completed;
      bucket.years[yearLevel].total += total;
    }

    const departmentLabels = Array.from(buckets.keys()).sort((a, b) => a.localeCompare(b));
    const departmentValues = departmentLabels.map((department) => {
      const bucket = buckets.get(department)!;
      return bucket.total > 0 ? Math.round((bucket.completed / bucket.total) * 1000) / 10 : 0;
    });
    const departmentYearBreakdown = Object.fromEntries(
      departmentLabels.map((department) => {
        const years = buckets.get(department)?.years || {};
        return [
          department,
          Object.fromEntries(
            Object.entries(years).map(([year, value]) => [
              Number(year),
              value.total > 0 ? Math.round((value.completed / value.total) * 1000) / 10 : 0,
            ]),
          ),
        ];
      }),
    );

    return {
      overall: grandTotal > 0 ? Math.round((completedTotal / grandTotal) * 1000) / 10 : 0,
      pending_counselors: pendingCounselors,
      department_labels: departmentLabels,
      department_values: departmentValues,
      department_year_breakdown: departmentYearBreakdown,
    };
  }

  const scopeRows = activityRows.map((row) => ({
    label: `${row.department} Y${row.year_level}`,
    value: row.completion_pct,
    row,
  }));

  let totalMessages = 0;

  for (const row of activityRows) {
    totalMessages += Number(row.total_messages || 0);
  }

  const marksCompletionOverview = buildCompletionOverview(
    activityRows,
    (row) => row.department,
    (row) => Number(row.year_level || 1),
    (row) => Math.min(Number(row.unique_students_messaged || 0), Number(row.student_count || 0)),
    (row) => Number(row.student_count || 0),
    (row) => Number(row.completion_pct || 0) < 100,
  );
  const noticeCompletionOverview = buildCompletionOverview(
    noticeRows,
    (row) => row.department,
    (row) => Number(row.year_level || 1),
    (row) => Number(row.completed_notice_count || 0),
    (row) => Number(row.total_notice_count || 0),
    (row) => Number(row.pending_notice_count || 0) > 0,
  );

  const leaderboard = activityRows
    .filter((item) => Number(item.student_count || 0) > 0)
    .sort((a, b) => {
      if (b.completion_pct !== a.completion_pct) return b.completion_pct - a.completion_pct;
      if (b.total_messages !== a.total_messages) return b.total_messages - a.total_messages;
      return a.name.localeCompare(b.name);
    })
    .slice(0, 10);

  const payload = {
    metrics: {
      departmentsCovered: departments.length,
      totalTests: 0,
      overallCompletion: marksCompletionOverview.overall,
      totalMessages,
    },
    completion_overview: marksCompletionOverview,
    notice_completion_overview: noticeCompletionOverview,
    counselor_activity: {
      labels: scopeRows.map((item) => item.label),
      values: scopeRows.map((item) => item.value),
    },
    leaderboard,
    recentTests: [],
  };
  if (authUser.role === 'admin') {
    return {
      ...payload,
      admin_status: await getAdminDashboardStatus(),
    };
  }
  return payload;
}

type ActivityScopeReportSection = {
  department: string;
  year_level: number;
  semester: string;
  test_name: string;
  stats: {
    total_counselors: number;
    complete: number;
    pending: number;
    avg_completion: number;
  };
  rows: ReturnType<typeof getCounselorActivityForTest>['rows'];
};

function getActivityScopeReport(
  authUser: ReturnType<typeof toAuthUser>,
  filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
  },
) {
  const visibleDepartments = getVisibleDepartmentsForActor(authUser);
  const yearsByDepartment = getScopedYearsByDepartment(authUser);
  const allowedScopes = getAllowedScopesForUser(authUser);
  const selectedDepartment = String(filters?.department || '').trim().toUpperCase();
  const selectedYear = Number(filters?.year || 0) || null;
  const selectedSemester = String(filters?.semester || '').trim();
  const selectedTestName = String(filters?.test_name || '').trim().toUpperCase();
  const testOrder = new Map([
    ['IAT 1', 1],
    ['IAT 2', 2],
    ['MODEL EXAM', 3],
  ]);

  const candidateDepartments = selectedDepartment
    ? visibleDepartments.filter((department) => department.code.toUpperCase() === selectedDepartment)
    : visibleDepartments;
  const sections: ActivityScopeReportSection[] = [];

  for (const department of candidateDepartments) {
    const departmentCode = String(department.code || '').trim().toUpperCase();
    const candidateYears = selectedYear
      ? (yearsByDepartment.get(departmentCode) || []).filter((year) => year === selectedYear)
      : Array.from(new Set(yearsByDepartment.get(departmentCode) || [])).sort((a, b) => a - b);

    for (const yearLevel of candidateYears) {
      const uploadedTests = getAllUniqueTests({
        filterDept: departmentCode,
        filterYearLevel: yearLevel,
        allowedScopes,
      }).filter((test) => {
        const semester = String(test.semester || '').trim();
        const testName = String(test.test_name || '').trim().toUpperCase();
        if (!['1', '2'].includes(semester)) return false;
        if (selectedSemester && semester !== selectedSemester) return false;
        if (selectedTestName && testName !== selectedTestName) return false;
        return true;
      });

      for (const test of uploadedTests) {
        const semester = String(test.semester || '').trim();
        const testName = String(test.test_name || '').trim().toUpperCase();
        const result = getCounselorActivityForTest(departmentCode, yearLevel, semester, testName, '', 'pending_first');
        sections.push({
          department: departmentCode,
          year_level: yearLevel,
          semester,
          test_name: testName,
          stats: result.stats,
          rows: result.rows,
        });
      }
    }
  }

  return sections.sort((a, b) => {
    const departmentCompare = a.department.localeCompare(b.department);
    if (departmentCompare !== 0) return departmentCompare;
    if (a.year_level !== b.year_level) return a.year_level - b.year_level;
    if (a.semester !== b.semester) return a.semester.localeCompare(b.semester);
    return (testOrder.get(a.test_name) || 99) - (testOrder.get(b.test_name) || 99);
  });
}

async function renderActivityScopePdfWithPython(payload: {
  generated_at: string;
  sections: ActivityScopeReportSection[];
}) {
  const scriptPath = resolve(SERVER_ROOT, 'scripts', 'generate_activity_scope_pdf.py');
  const candidates = process.platform === 'win32'
    ? [
      { command: 'python', args: [scriptPath] },
      { command: 'py', args: ['-3', scriptPath] },
    ]
    : [
      { command: 'python3', args: [scriptPath] },
      { command: 'python', args: [scriptPath] },
    ];

  let lastError = 'Python renderer is unavailable.';
  for (const candidate of candidates) {
    try {
      const pdfBuffer = await new Promise<Buffer>((resolvePromise, rejectPromise) => {
        const child = spawn(candidate.command, candidate.args, {
          cwd: SERVER_ROOT,
          env: {
            ...process.env,
            PYTHONIOENCODING: 'utf-8',
          },
          stdio: ['pipe', 'pipe', 'pipe'],
        });
        const stdoutChunks: Buffer[] = [];
        const stderrChunks: Buffer[] = [];

        child.stdout.on('data', (chunk) => stdoutChunks.push(Buffer.from(chunk)));
        child.stderr.on('data', (chunk) => stderrChunks.push(Buffer.from(chunk)));
        child.on('error', (error) => rejectPromise(error));
        child.on('close', (code) => {
          if (code === 0) {
            resolvePromise(Buffer.concat(stdoutChunks));
            return;
          }
          rejectPromise(new Error(Buffer.concat(stderrChunks).toString('utf8').trim() || `Python exited with code ${code}.`));
        });

        child.stdin.write(JSON.stringify(payload));
        child.stdin.end();
      });

      if (!pdfBuffer.length) {
        throw new Error('Python renderer returned an empty PDF.');
      }
      return pdfBuffer;
    } catch (error) {
      lastError = error instanceof Error ? error.message : 'Python renderer failed.';
    }
  }

  throw new Error(lastError);
}

async function upsertEnvValues(envPath: string, values: Record<string, string>) {
  let content = '';
  try {
    content = await readFile(envPath, 'utf-8');
  } catch {
    content = '';
  }

  const lines = content ? content.split(/\r?\n/) : [];
  const nextValues = new Map(Object.entries(values || {}));
  const updated = lines.map((line) => {
    const match = line.match(/^\s*([A-Za-z_][A-Za-z0-9_]*)\s*=/);
    if (!match) return line;
    const key = match[1];
    if (!nextValues.has(key)) return line;
    const value = nextValues.get(key) || '';
    nextValues.delete(key);
    return `${key}=${value}`;
  });

  for (const [key, value] of nextValues.entries()) {
    updated.push(`${key}=${value}`);
  }

  await writeFile(envPath, `${updated.filter((line) => line !== undefined).join('\n').replace(/\n{3,}/g, '\n\n')}\n`, 'utf-8');
}

function getBackupStorageMode(config = getAppConfig()) {
  return String(config.backup_storage_mode || 'local').trim().toLowerCase() === 'gdrive' ? 'gdrive' : 'local';
}

async function collectFilesRecursively(rootDir: string, currentDir = rootDir, prefix = ''): Promise<Array<{ absolutePath: string; relativePath: string }>> {
  const items = await readdir(currentDir, { withFileTypes: true }).catch(() => []);
  const files: Array<{ absolutePath: string; relativePath: string }> = [];
  for (const item of items) {
    const absolutePath = resolve(currentDir, item.name);
    const relativePath = prefix ? `${prefix}/${item.name}` : item.name;
    if (item.isDirectory()) {
      files.push(...await collectFilesRecursively(rootDir, absolutePath, relativePath));
      continue;
    }
    if (!item.isFile()) continue;
    files.push({ absolutePath, relativePath: relativePath.replace(/\\/g, '/') });
  }
  return files;
}

function guessDriveMimeType(fileName: string) {
  const normalized = String(fileName || '').trim().toLowerCase();
  if (normalized.endsWith('.db')) return 'application/x-sqlite3';
  if (normalized.endsWith('.env') || !extname(normalized)) return 'text/plain';
  if (normalized.endsWith('.pdf')) return 'application/pdf';
  if (normalized.endsWith('.jpg') || normalized.endsWith('.jpeg')) return 'image/jpeg';
  if (normalized.endsWith('.png')) return 'image/png';
  if (normalized.endsWith('.gif')) return 'image/gif';
  if (normalized.endsWith('.webp')) return 'image/webp';
  if (normalized.endsWith('.mp4')) return 'video/mp4';
  if (normalized.endsWith('.mov')) return 'video/quicktime';
  if (normalized.endsWith('.xlsx')) return 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet';
  if (normalized.endsWith('.xls')) return 'application/vnd.ms-excel';
  if (normalized.endsWith('.docx')) return 'application/vnd.openxmlformats-officedocument.wordprocessingml.document';
  if (normalized.endsWith('.doc')) return 'application/msword';
  return 'application/octet-stream';
}

async function uploadLocalFileToDrive(
  localPath: string,
  pathSegments: string[],
  fileName: string,
  overwrite = true,
  driveSettings = getGoogleDriveSettings(),
) {
  await uploadDriveFileToPath({
    pathSegments,
    name: fileName,
    mimeType: guessDriveMimeType(fileName),
    content: await readFile(localPath),
    overwrite,
  }, driveSettings);
}

async function syncLocalDirectoryToDrive(
  localDir: string,
  pathSegments: string[],
  options: { clearFirst?: boolean } = {},
  driveSettings = getGoogleDriveSettings(),
) {
  if (options.clearFirst) {
    await clearDrivePath(pathSegments, driveSettings);
  }

  try {
    const localStat = await stat(localDir);
    if (!localStat.isDirectory()) return;
  } catch {
    return;
  }

  const files = await collectFilesRecursively(localDir).catch(() => []);
  for (const file of files) {
    const segments = file.relativePath.split('/').filter(Boolean);
    const fileSegment = segments.pop();
    if (!fileSegment) continue;
    await uploadLocalFileToDrive(
      file.absolutePath,
      [...pathSegments, ...segments],
      fileSegment,
      true,
      driveSettings,
    );
  }
}

async function syncDriveDirectoryToLocal(
  pathSegments: string[],
  localDir: string,
  options: { clearFirst?: boolean; skipIfMissing?: boolean } = {},
  driveSettings = getGoogleDriveSettings(),
) {
  const folderId = await findDrivePath(pathSegments, driveSettings);
  if (!folderId) {
    if (options.skipIfMissing) return false;
    await rm(localDir, { recursive: true, force: true }).catch(() => undefined);
    await mkdir(localDir, { recursive: true });
    return false;
  }

  if (options.clearFirst !== false) {
    await rm(localDir, { recursive: true, force: true }).catch(() => undefined);
  }
  await mkdir(localDir, { recursive: true });

  const entries = await listDriveEntriesInPath(pathSegments, driveSettings);
  for (const entry of entries) {
    const targetPath = resolve(localDir, entry.name);
    if (entry.isFolder) {
      await syncDriveDirectoryToLocal([...pathSegments, entry.name], targetPath, { clearFirst: true }, driveSettings);
      continue;
    }
    await mkdir(dirname(targetPath), { recursive: true });
    await writeFile(targetPath, await downloadDriveFileFromPath(pathSegments, entry.name, driveSettings));
  }
  return true;
}

async function createRuntimeSnapshot(snapshotDir: string) {
  await rm(snapshotDir, { recursive: true, force: true }).catch(() => undefined);
  await mkdir(snapshotDir, { recursive: true });
  try {
    await copyFile(APP_ENV_FILE, resolve(snapshotDir, '.env'));
  } catch {
    // Rebuild .env is optional in snapshots.
  }
  try {
    await stat(NOTICE_UPLOAD_ROOT);
    await cp(NOTICE_UPLOAD_ROOT, resolve(snapshotDir, 'notice_assets'), { recursive: true, force: true });
  } catch {
    // Notice assets may not exist yet.
  }
}

async function syncRuntimeDataMirrorToDrive(driveSettings = getGoogleDriveSettings()) {
  await uploadLocalFileToDrive(SHINE_DB_PATH, [], 'rmkcet.db', true, driveSettings);
  await syncLocalDirectoryToDrive(NOTICE_UPLOAD_ROOT, ['notice_assets'], { clearFirst: true }, driveSettings);
}

async function migrateLegacyDriveZipArtifacts(driveSettings = getGoogleDriveSettings()) {
  const rootEntries = await listDriveEntriesInPath([], driveSettings);
  const legacyArtifacts = rootEntries.filter((entry) => !entry.isFolder && /\.zip$/i.test(entry.name));
  for (const artifact of legacyArtifacts) {
    const normalized = String(artifact.name || '').toLowerCase();
    const targetFolder = normalized.startsWith('archive_') ? 'archives' : 'backups';
    const targetDbName = String(artifact.name || '').replace(/\.zip$/i, '.db');
    const buffer = await downloadDriveFileFromPath([], artifact.name, driveSettings);
    const zip = await JSZip.loadAsync(buffer);
    const databaseEntry = zip.file('database.db');
    if (!databaseEntry) continue;

    await uploadDriveFileToPath({
      pathSegments: [targetFolder],
      name: targetDbName,
      mimeType: 'application/x-sqlite3',
      content: await databaseEntry.async('nodebuffer'),
      overwrite: true,
    }, driveSettings);

    const snapshotPath = [targetFolder, `${targetDbName}${BACKUP_SNAPSHOT_SUFFIX}`];
    await clearDrivePath(snapshotPath, driveSettings);

    const envEntry = zip.file('.env');
    if (envEntry) {
      await uploadDriveFileToPath({
        pathSegments: snapshotPath,
        name: '.env',
        mimeType: 'text/plain',
        content: await envEntry.async('nodebuffer'),
        overwrite: true,
      }, driveSettings);
    }

    const noticeEntries = Object.values(zip.files).filter((entry) => entry.name.startsWith('notice_assets/') && !entry.dir);
    for (const entry of noticeEntries) {
      const relativeSegments = entry.name.slice('notice_assets/'.length).split('/').filter(Boolean);
      const fileSegment = relativeSegments.pop();
      if (!fileSegment) continue;
      await uploadDriveFileToPath({
        pathSegments: [...snapshotPath, 'notice_assets', ...relativeSegments],
        name: fileSegment,
        mimeType: guessDriveMimeType(fileSegment),
        content: await entry.async('nodebuffer'),
        overwrite: true,
      }, driveSettings);
    }

    await deleteDriveFileFromPath([], artifact.name, driveSettings).catch(() => undefined);
  }
}

async function listLocalBackupFiles() {
  await mkdir(BACKUP_DIR, { recursive: true });
  const items = await readdir(BACKUP_DIR, { withFileTypes: true });
  const autoBackupFiles: Array<{ name: string; size_kb: number; modified: string }> = [];
  const backupFiles: Array<{ name: string; size_kb: number; modified: string }> = [];
  for (const item of items) {
    if (!item.isFile()) continue;
    const filePath = resolve(BACKUP_DIR, item.name);
    const fileStat = await stat(filePath);
    const entry = {
      name: item.name,
      size_kb: Math.floor(fileStat.size / 1024),
      modified: new Date(fileStat.mtime).toISOString().slice(0, 16).replace('T', ' '),
    };
    if (isAutomaticBackupFileName(item.name)) autoBackupFiles.push(entry);
    else backupFiles.push(entry);
  }
  autoBackupFiles.sort((a, b) => b.name.localeCompare(a.name));
  backupFiles.sort((a, b) => b.name.localeCompare(a.name));
  return { autoBackupFiles, backupFiles };
}

async function listLocalArchiveFiles() {
  await mkdir(ARCHIVE_DIR, { recursive: true });
  const items = await readdir(ARCHIVE_DIR, { withFileTypes: true });
  const archiveFiles: Array<{ name: string; size_kb: number; modified: string }> = [];
  for (const item of items) {
    if (!item.isFile()) continue;
    const filePath = resolve(ARCHIVE_DIR, item.name);
    const fileStat = await stat(filePath);
    archiveFiles.push({
      name: item.name,
      size_kb: Math.floor(fileStat.size / 1024),
      modified: new Date(fileStat.mtime).toISOString().slice(0, 16).replace('T', ' '),
    });
  }
  archiveFiles.sort((a, b) => b.name.localeCompare(a.name));
  return archiveFiles;
}

async function listDriveBackupFiles() {
  await migrateLegacyDriveZipArtifacts();
  const files = await listDriveFilesInPath(['backups']);
  const databaseFiles = files.filter((file) => /\.db$/i.test(String(file.name || '')));
  const autoBackupFiles = databaseFiles.filter((file) => isAutomaticBackupFileName(file.name));
  const backupFiles = databaseFiles.filter((file) => !isAutomaticBackupFileName(file.name) && !String(file.name || '').toLowerCase().startsWith('archive_'));
  autoBackupFiles.sort((a, b) => b.name.localeCompare(a.name));
  backupFiles.sort((a, b) => b.name.localeCompare(a.name));
  return { autoBackupFiles, backupFiles };
}

async function listDriveArchiveFiles() {
  await migrateLegacyDriveZipArtifacts();
  const files = await listDriveFilesInPath(['archives']);
  const archiveFiles = files.filter((file) => /\.db$/i.test(String(file.name || '')) && String(file.name || '').toLowerCase().startsWith('archive_'));
  archiveFiles.sort((a, b) => b.name.localeCompare(a.name));
  return archiveFiles;
}

async function listBackupFiles() {
  if (getBackupStorageMode() === 'gdrive') {
    return listDriveBackupFiles();
  }
  return listLocalBackupFiles();
}

async function listArchiveFiles() {
  if (getBackupStorageMode() === 'gdrive') {
    return listDriveArchiveFiles();
  }
  return listLocalArchiveFiles();
}

async function performDatabaseBackup(batchName: string, overwrite = false, autoGenerated = false) {
  const safeBatch = String(batchName || 'batch').replace(/[^0-9A-Za-z_-]/g, '_');
  const fileName = autoGenerated ? `${AUTO_BACKUP_FILE_PREFIX}${safeBatch}.db` : `rmkcet_shine_${safeBatch}.db`;
  if (getBackupStorageMode() === 'gdrive') {
    const driveSettings = getGoogleDriveSettings();
    const tempRoot = await mkdtemp(resolve(tmpdir(), 'shine-drive-backup-'));
    const tempDbPath = resolve(tempRoot, fileName);
    const tempSnapshotDir = resolve(tempRoot, `${fileName}${BACKUP_SNAPSHOT_SUFFIX}`);
    try {
      await db.backup(tempDbPath);
      await createRuntimeSnapshot(tempSnapshotDir);
      await uploadLocalFileToDrive(tempDbPath, ['backups'], fileName, overwrite, driveSettings);
      await syncLocalDirectoryToDrive(
        tempSnapshotDir,
        ['backups', `${fileName}${BACKUP_SNAPSHOT_SUFFIX}`],
        { clearFirst: true },
        driveSettings,
      );
      await syncRuntimeDataMirrorToDrive(driveSettings);
    } finally {
      await rm(tempRoot, { recursive: true, force: true }).catch(() => undefined);
    }
    return `gdrive:backups/${fileName}`;
  }

  await mkdir(BACKUP_DIR, { recursive: true });
  const targetPath = resolve(BACKUP_DIR, fileName);
  const snapshotDir = getBackupSnapshotDir(targetPath);
  try {
    await stat(targetPath);
    if (!overwrite) {
      throw new Error('Backup for this batch already exists. Enable overwrite to replace it.');
    }
  } catch {
    // Missing is fine.
  }
  if (overwrite) {
    await rm(snapshotDir, { recursive: true, force: true });
  }
  await db.backup(targetPath);
  await mkdir(snapshotDir, { recursive: true });
  try {
    await copyFile(APP_ENV_FILE, resolve(snapshotDir, '.env'));
  } catch {
    // Rebuild .env is optional in backups.
  }
  try {
    await stat(NOTICE_UPLOAD_ROOT);
    await cp(NOTICE_UPLOAD_ROOT, resolve(snapshotDir, 'notice_assets'), { recursive: true, force: true });
  } catch {
    // Notice assets may not exist yet.
  }
  return targetPath;
}

async function performYearArchive(archiveLabel: string, overwrite = false) {
  const safeLabel = String(archiveLabel || '').trim().replace(/[^0-9A-Za-z_-]/g, '_');
  if (!safeLabel) {
    throw new Error('Academic year range is required.');
  }
  const fileName = `archive_${safeLabel}.db`;
  if (getBackupStorageMode() === 'gdrive') {
    const driveSettings = getGoogleDriveSettings();
    const tempRoot = await mkdtemp(resolve(tmpdir(), 'shine-drive-archive-'));
    const tempDbPath = resolve(tempRoot, fileName);
    const tempSnapshotDir = resolve(tempRoot, `${fileName}${BACKUP_SNAPSHOT_SUFFIX}`);
    try {
      await db.backup(tempDbPath);
      await createRuntimeSnapshot(tempSnapshotDir);
      await uploadLocalFileToDrive(tempDbPath, ['archives'], fileName, overwrite, driveSettings);
      await syncLocalDirectoryToDrive(
        tempSnapshotDir,
        ['archives', `${fileName}${BACKUP_SNAPSHOT_SUFFIX}`],
        { clearFirst: true },
        driveSettings,
      );
    } finally {
      await rm(tempRoot, { recursive: true, force: true }).catch(() => undefined);
    }
    return `gdrive:archives/${fileName}`;
  }

  await mkdir(ARCHIVE_DIR, { recursive: true });
  const targetPath = resolve(ARCHIVE_DIR, fileName);
  const snapshotDir = getBackupSnapshotDir(targetPath);
  try {
    await stat(targetPath);
    if (!overwrite) {
      throw new Error('Archive for this academic year already exists. Enable overwrite to replace it.');
    }
  } catch {
    // Missing is fine.
  }
  if (overwrite) {
    await rm(snapshotDir, { recursive: true, force: true });
  }
  await db.backup(targetPath);
  await mkdir(snapshotDir, { recursive: true });
  try {
    await copyFile(APP_ENV_FILE, resolve(snapshotDir, '.env'));
  } catch {
    // Optional.
  }
  try {
    await stat(NOTICE_UPLOAD_ROOT);
    await cp(NOTICE_UPLOAD_ROOT, resolve(snapshotDir, 'notice_assets'), { recursive: true, force: true });
  } catch {
    // Optional.
  }
  return targetPath;
}

async function latestBackupIsRecentEnough(maxAgeMinutes = 30, dbDriftToleranceSeconds = 300) {
  try {
    const { autoBackupFiles, backupFiles } = await listBackupFiles();
    const all = [...autoBackupFiles, ...backupFiles];
    if (!all.length) return false;
    if (getBackupStorageMode() === 'gdrive') {
      const latest = all
        .map((item) => Date.parse(String(item.modified || '').replace(' ', 'T')))
        .filter((value) => Number.isFinite(value))
        .sort((a, b) => b - a)[0];
      if (!latest) return false;
      return latest >= Date.now() - Math.max(1, maxAgeMinutes) * 60 * 1000;
    }
    const stats = await Promise.all(all.map(async (item) => ({ item, stat: await stat(resolve(BACKUP_DIR, item.name)) })));
    stats.sort((a, b) => b.stat.mtimeMs - a.stat.mtimeMs);
    const latest = stats[0].stat;
    const now = Date.now();
    if (latest.mtimeMs >= now - Math.max(1, maxAgeMinutes) * 60 * 1000) return true;
    const dbStat = await stat(SHINE_DB_PATH);
    return latest.mtimeMs >= dbStat.mtimeMs - Math.max(0, dbDriftToleranceSeconds) * 1000;
  } catch {
    return false;
  }
}

async function migrateStorageArtifacts(
  fromMode: 'local' | 'gdrive',
  toMode: 'local' | 'gdrive',
  driveSettings = getGoogleDriveSettings(),
) {
  if (fromMode === toMode) return;

  if (fromMode === 'local' && toMode === 'gdrive') {
    await clearDrivePath(['backups'], driveSettings);
    await clearDrivePath(['archives'], driveSettings);
    await clearDrivePath(['notice_assets'], driveSettings);

    await syncLocalDirectoryToDrive(BACKUP_DIR, ['backups'], { clearFirst: false }, driveSettings);
    await syncLocalDirectoryToDrive(ARCHIVE_DIR, ['archives'], { clearFirst: false }, driveSettings);
    await syncRuntimeDataMirrorToDrive(driveSettings);

    await rm(BACKUP_DIR, { recursive: true, force: true }).catch(() => undefined);
    await rm(ARCHIVE_DIR, { recursive: true, force: true }).catch(() => undefined);
    await mkdir(BACKUP_DIR, { recursive: true });
    await mkdir(ARCHIVE_DIR, { recursive: true });
    return;
  }

  if (fromMode === 'gdrive' && toMode === 'local') {
    await migrateLegacyDriveZipArtifacts(driveSettings);
    await syncDriveDirectoryToLocal(['backups'], BACKUP_DIR, { clearFirst: true }, driveSettings);
    await syncDriveDirectoryToLocal(['archives'], ARCHIVE_DIR, { clearFirst: true }, driveSettings);

    await clearDrivePath(['backups'], driveSettings);
    await clearDrivePath(['archives'], driveSettings);
    await clearDrivePath(['notice_assets'], driveSettings);
    await deleteDriveFileFromPath([], 'backups', driveSettings).catch(() => undefined);
    await deleteDriveFileFromPath([], 'archives', driveSettings).catch(() => undefined);
    await deleteDriveFileFromPath([], 'notice_assets', driveSettings).catch(() => undefined);
    await deleteDriveFileFromPath([], 'rmkcet.db', driveSettings).catch(() => undefined);
  }
}

async function clearExamDatabaseOnly() {
  db.exec(`
    PRAGMA foreign_keys = OFF;
    DELETE FROM counselor_mark_overrides;
    DELETE FROM sent_messages;
    DELETE FROM notice_deliveries;
    DELETE FROM notice_attachments;
    DELETE FROM notice_scopes;
    DELETE FROM notices;
    DELETE FROM student_marks;
    DELETE FROM test_metadata;
    DELETE FROM tests;
    DELETE FROM semesters;
    DELETE FROM batches;
    DELETE FROM chief_admin_scopes WHERE chief_admin_email IN (SELECT email FROM users WHERE LOWER(COALESCE(role,'')) NOT IN ('admin','principal'));
    DELETE FROM counselor_students WHERE counselor_email IN (SELECT email FROM users WHERE LOWER(COALESCE(role,'')) NOT IN ('admin','principal'));
    DELETE FROM active_sessions WHERE user_email IN (SELECT email FROM users WHERE LOWER(COALESCE(role,'')) NOT IN ('admin','principal'));
    DELETE FROM users WHERE LOWER(COALESCE(role,'')) NOT IN ('admin','principal');
    PRAGMA foreign_keys = ON;
  `);
}

function finalizeLogin(c: Context, userRow: Record<string, unknown>, forceLogoutOthers: boolean, authMethod = 'password') {
  const appConfig = getAppConfig();
  const sessionId = registerSession(
    String(userRow.email || '').toLowerCase(),
    c.req.header('x-forwarded-for') || c.req.header('x-real-ip') || '',
    c.req.header('user-agent') || '',
    forceLogoutOthers,
    authMethod,
  );

  setCookie(c, SESSION_COOKIE, sessionId, {
    path: '/',
    httpOnly: true,
    sameSite: 'Lax',
    maxAge: sessionCookieMaxAge(appConfig),
  });

  return {
    success: true,
    user: toAuthUser(userRow),
  };
}

app.use(
  '/api/*',
  cors({
    origin: CLIENT_ORIGIN,
    allowHeaders: ['Content-Type'],
    allowMethods: ['GET', 'POST', 'OPTIONS'],
    credentials: true,
  }),
);

app.use('/api/*', async (c, next) => {
  const startedAt = Date.now();
  const sessionId = getCookie(c, SESSION_COOKIE) || '';
  if (sessionId) {
    const user = validateSession(sessionId);
    if (user) {
      c.set('sessionAuthUser', user);
      c.set('sessionId', sessionId);
      const previewEmail = String(getCookie(c, TEST_MODE_COOKIE) || '').trim().toLowerCase();
      if (user.role === 'admin' && previewEmail) {
        const previewUserRow = getUserByEmail(previewEmail);
        if (previewUserRow) {
          const previewUser = toAuthUser(previewUserRow);
          c.set('realAuthUser', user);
          c.set('authUser', previewUser);
          c.set('testModeTarget', previewUser);
        } else {
          deleteCookie(c, TEST_MODE_COOKIE, { path: '/' });
          c.set('authUser', user);
        }
      } else {
        c.set('authUser', user);
      }
    }
  }
  await next();
  appendServerConsoleLine(`${c.req.method} ${new URL(c.req.url).pathname} -> ${c.res.status} (${Date.now() - startedAt} ms)`);
});

app.get('/api/health', (c) => c.json({ ok: true, app: APP_NAME, version: APP_VERSION }));

app.get('/api/auth/me', (c) => {
  const authUser = c.get('authUser') || null;
  return c.json({ user: authUser });
});

app.get('/api/footer/templates', async (c) => {
  const templateCards = Object.entries(TEMPLATE_FILE_MAP)
    .map(([templateKey, template]) => `
      <article class="template-card">
        <span class="template-pill">Excel Template</span>
        <div>
          <h2 class="template-card-title">${template.title}</h2>
          <p class="template-card-copy">${template.description}</p>
        </div>
        <a class="template-download-btn" href="/api/footer/templates/${templateKey}" download>
          Download ${template.title}
        </a>
      </article>
    `)
    .join('');

  return c.html(`<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <title>Templates - ${APP_NAME}</title>
    <style>${FOOTER_CREDITS_INLINE_CSS}</style>
  </head>
  <body>
    <section class="credits-page">
      <div class="credits-page-hero">
        <div>
          <p class="credits-page-kicker">Resources</p>
          <h1 class="credits-page-title">Download Templates</h1>
          <p class="credits-page-subtitle">Use the official rebuild copies of the counselor, marks, and student spreadsheet templates.</p>
        </div>
        <button class="credits-back-btn" type="button" onclick="if (window.history.length > 1) { window.history.back(); } else { window.close(); }">Back</button>
      </div>
      <div class="credits-page-body">
        <div class="template-grid">${templateCards}</div>
      </div>
    </section>
  </body>
</html>`);
});

app.get('/api/footer/templates/:templateKey', async (c) => {
  const templateKey = String(c.req.param('templateKey') || '').trim() as keyof typeof TEMPLATE_FILE_MAP;
  const template = TEMPLATE_FILE_MAP[templateKey];
  if (!template) return c.text('Template not found.', 404);
  const filePath = resolve(CLIENT_PUBLIC_ASSETS_ROOT, template.fileName);
  const data = await readFile(filePath);
  c.header('Content-Type', 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet');
  c.header('Content-Disposition', `attachment; filename="${template.fileName}"`);
  return new Response(new Uint8Array(data));
});

app.get('/api/footer/credits', async (c) => {
  const creditsPath = resolve(CLIENT_PUBLIC_ASSETS_ROOT, 'credits_compiled.html');
  let compiledCreditsHtml = '';
  try {
    compiledCreditsHtml = await readFile(creditsPath, 'utf8');
  } catch {
    compiledCreditsHtml = `
      <section class="credits-compiled-shell">
        <div class="credits-compiled-header">
          <h2 class="credits-compiled-title">Project Credits</h2>
          <p class="credits-compiled-subtitle">Compiled credits are temporarily unavailable.</p>
        </div>
        <pre class="credits-compiled-fallback">Credits content could not be loaded from the rebuild assets.</pre>
      </section>
    `;
  }

  return c.html(`<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <link rel="preconnect" href="https://fonts.googleapis.com" />
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin />
    <link href="https://fonts.googleapis.com/css2?family=Inter:wght@300;400;500;600;700;800&display=swap" rel="stylesheet" />
    <title>Credits - ${APP_NAME}</title>
    <style>${FOOTER_CREDITS_INLINE_CSS}</style>
  </head>
  <body>
    <section class="credits-page">
      <div class="credits-page-hero">
        <div>
          <p class="credits-page-kicker">Acknowledgements</p>
          <h1 class="credits-page-title">Project Credits</h1>
          <p class="credits-page-subtitle">Compiled from the credits source file and rendered as a professional publication view.</p>
        </div>
        <a class="credits-back-btn" href="${CLIENT_ORIGIN}" onclick="if (window.history.length > 1) { window.history.back(); return false; }">
          <span style="margin-right:8px;">&larr;</span>Back
        </a>
      </div>
      <div class="credits-page-body">${compiledCreditsHtml}</div>
    </section>
  </body>
</html>`);
});

function getStaticMimeType(filePath: string) {
  switch (extname(filePath).toLowerCase()) {
    case '.html':
      return 'text/html; charset=utf-8';
    case '.js':
      return 'application/javascript; charset=utf-8';
    case '.css':
      return 'text/css; charset=utf-8';
    case '.json':
      return 'application/json; charset=utf-8';
    case '.svg':
      return 'image/svg+xml';
    case '.png':
      return 'image/png';
    case '.jpg':
    case '.jpeg':
      return 'image/jpeg';
    case '.gif':
      return 'image/gif';
    case '.webp':
      return 'image/webp';
    case '.ico':
      return 'image/x-icon';
    case '.woff':
      return 'font/woff';
    case '.woff2':
      return 'font/woff2';
    default:
      return 'application/octet-stream';
  }
}

app.get('/api/bootstrap', (c) => {
  const authUser = c.get('authUser') || null;
  const sessionAuthUser = c.get('sessionAuthUser') || authUser || null;
  const testModeTarget = c.get('testModeTarget') || null;
  const appConfig = getAppConfig();
  const safeAppConfig = sanitizeAppConfigForClient(appConfig, authUser);
  const authUi = getAuthUiConfig(authUser, appConfig);
  const now = new Date();
  const nowLabel = now
    .toLocaleString('en-GB', {
      day: '2-digit',
      month: 'short',
      hour: '2-digit',
      minute: '2-digit',
      hour12: false,
    })
    .replace(',', '');

  const counselorTests = authUser?.role === 'counselor' ? getVisibleTestsForCounselor(authUser.email) : [];
  const counselorOverview = authUser?.role === 'counselor' ? buildCounselorOverviewPayload(authUser.email) : null;

  return c.json({
    appName: APP_NAME,
    appVersion: APP_VERSION,
    appConfig: safeAppConfig,
    authUi,
    nowLabel,
    user: authUser,
    testMode: {
      active: Boolean(testModeTarget),
      sessionUser: sessionAuthUser,
      targetUser: testModeTarget,
    },
    navTabs: authUser ? allowedTabsForRole(authUser.role) : [],
    defaultTab: authUser ? defaultTabForRole(authUser.role) : 'reports',
    metrics: getDashboardMetrics(authUser),
    counselorOverview,
    counselorTests,
  });
});

app.get('/api/dashboard/overview', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  return c.json(await buildDashboardOverview(authUser));
});

app.post('/api/auth/login', async (c) => {
  const body = (await c.req
    .json<{ identifier?: string; password?: string; forceLogout?: boolean }>()
    .catch(() => ({}))) as {
    identifier?: string;
    password?: string;
    forceLogout?: boolean;
  };
  const identifier = String(body.identifier || '').trim();
  const password = String(body.password || '');
  const forceLogout = !!body.forceLogout;

  if (!identifier || !password) {
    return c.json({ error: 'Identifier and password are required.' }, 400);
  }

  const userRow = getUserByIdentifier(identifier);
  if (!userRow || !verifyPassword(password, String(userRow.password_hash || ''))) {
    return c.json({ error: 'Invalid credentials.' }, 401);
  }

  const userEmail = String(userRow.email || '').toLowerCase();
  const access = checkUserAccess(userEmail);
  if (!access.allowed) {
    return c.json({ error: access.message }, 403);
  }

  const appConfig = getAppConfig();
  const allowConcurrent = String(appConfig.allow_concurrent_sessions || 'false').toLowerCase() === 'true';
  if (!allowConcurrent && !forceLogout) {
    const activeSession = getActiveSessionForUser(userEmail);
    if (activeSession) {
      return c.json(
        {
          error: 'Active session detected.',
          requiresForceLogout: true,
          existingSession: activeSession,
        },
        409,
      );
    }
  }

  if (!isLoginOtpRequiredForUser(userRow, appConfig)) {
    return c.json(finalizeLogin(c, userRow, !!forceLogout || !allowConcurrent));
  }

  if (getSmtpStatus().state !== 'ready') {
    return c.json({ error: 'SMTP is not ready. Login OTP delivery is unavailable.' }, 400);
  }

  const challenge = await createLoginOtpChallenge(c, userRow, !!forceLogout || !allowConcurrent);
  if (!challenge) {
    return c.json({ error: 'Unable to send login OTP. Verify SMTP settings and try again.' }, 400);
  }
  return c.json({
    success: true,
    requiresOtp: true,
    maskedEmail: challenge.maskedEmail,
  });
});

app.post('/api/auth/login/verify-otp', async (c) => {
  const body = (await c.req.json<{ otp_code?: string }>().catch(() => ({}))) as { otp_code?: string };
  const otpCode = String(body.otp_code || '').trim();
  const token = getCookie(c, LOGIN_OTP_COOKIE) || '';
  cleanupExpiredChallengeMap(pendingLoginOtpChallenges);
  const challenge = token ? pendingLoginOtpChallenges.get(token) : null;
  if (!challenge || !isOtpCookieFresh(challenge)) {
    if (token) pendingLoginOtpChallenges.delete(token);
    clearChallengeCookie(c, LOGIN_OTP_COOKIE);
    return c.json({ error: 'Login OTP expired. Please sign in again.' }, 400);
  }
  if (!otpCode || hashOtp(otpCode) !== challenge.otpHash) {
    pendingLoginOtpChallenges.set(token, { ...challenge, invalidAttempts: Number(challenge.invalidAttempts || 0) + 1 });
    return c.json({ error: 'Invalid OTP. Please try again.' }, 401);
  }
  const userRow = getUserByEmail(challenge.email);
  if (!userRow) {
    pendingLoginOtpChallenges.delete(token);
    clearChallengeCookie(c, LOGIN_OTP_COOKIE);
    return c.json({ error: 'User not found. Please sign in again.' }, 404);
  }
  const access = checkUserAccess(challenge.email);
  if (!access.allowed) {
    pendingLoginOtpChallenges.delete(token);
    clearChallengeCookie(c, LOGIN_OTP_COOKIE);
    return c.json({ error: access.message }, 403);
  }
  pendingLoginOtpChallenges.delete(token);
  clearChallengeCookie(c, LOGIN_OTP_COOKIE);
  return c.json(finalizeLogin(c, userRow, challenge.forceLogoutOthers));
});

app.post('/api/auth/login/resend-otp', async (c) => {
  const token = getCookie(c, LOGIN_OTP_COOKIE) || '';
  cleanupExpiredChallengeMap(pendingLoginOtpChallenges);
  const challenge = token ? pendingLoginOtpChallenges.get(token) : null;
  if (!challenge || !isOtpCookieFresh(challenge)) {
    if (token) pendingLoginOtpChallenges.delete(token);
    clearChallengeCookie(c, LOGIN_OTP_COOKIE);
    return c.json({ error: 'Login OTP expired. Please sign in again.' }, 400);
  }
  try {
    const refreshed = await refreshLoginOtpChallenge(c, token, challenge);
    return c.json({ success: true, maskedEmail: refreshed.maskedEmail });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Unable to resend OTP.' }, 400);
  }
});

app.post('/api/auth/login/cancel-otp', (c) => {
  const token = getCookie(c, LOGIN_OTP_COOKIE) || '';
  if (token) pendingLoginOtpChallenges.delete(token);
  clearChallengeCookie(c, LOGIN_OTP_COOKIE);
  return c.json({ success: true });
});

app.post('/api/auth/logout', (c) => {
  const sessionId = c.get('sessionId') || getCookie(c, SESSION_COOKIE) || '';
  if (sessionId) {
    logoutSession(sessionId, 'logout');
  }
  deleteCookie(c, SESSION_COOKIE, { path: '/' });
  deleteCookie(c, TEST_MODE_COOKIE, { path: '/' });
  clearChallengeCookie(c, LOGIN_OTP_COOKIE);
  clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
  clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
  return c.json({ success: true });
});

app.post('/api/test-mode/start', async (c) => {
  const sessionAuthUser = c.get('sessionAuthUser') || c.get('authUser');
  if (!sessionAuthUser) return c.json({ error: 'Unauthorized' }, 401);
  if (sessionAuthUser.role !== 'admin') return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ email?: string }>().catch(() => ({}))) as { email?: string };
  const email = String(body.email || '').trim().toLowerCase();
  if (!email) return c.json({ error: 'User email is required.' }, 400);
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'Selected user was not found.' }, 404);
  setCookie(c, TEST_MODE_COOKIE, email, {
    path: '/',
    httpOnly: true,
    sameSite: 'Lax',
    maxAge: sessionCookieMaxAge(getAppConfig()),
  });
  return c.json({ success: true, user: toAuthUser(target) });
});

app.post('/api/test-mode/stop', (c) => {
  const sessionAuthUser = c.get('sessionAuthUser') || c.get('realAuthUser') || c.get('authUser');
  if (!sessionAuthUser) return c.json({ error: 'Unauthorized' }, 401);
  if (sessionAuthUser.role !== 'admin') return c.json({ error: 'Forbidden' }, 403);
  deleteCookie(c, TEST_MODE_COOKIE, { path: '/' });
  return c.json({ success: true });
});

app.post('/api/auth/password-reset/request', async (c) => {
  const body = (await c.req.json<{ identifier?: string }>().catch(() => ({}))) as { identifier?: string };
  const identifier = String(body.identifier || '').trim();
  if (!identifier) return c.json({ error: 'Email or name is required.' }, 400);
  if (getSmtpStatus().state !== 'ready') {
    return c.json({ error: 'SMTP is not ready. Password reset requires OTP email delivery.' }, 400);
  }
  const userRow = getUserByIdentifier(identifier);
  if (!userRow) return c.json({ error: 'No account matched that email or name.' }, 404);
  const email = String(userRow.email || '').trim().toLowerCase();
  const access = checkUserAccess(email);
  if (!access.allowed) return c.json({ error: access.message }, 403);
  const challenge = await createPasswordResetChallenge(c, userRow);
  if (!challenge) {
    return c.json({ error: 'Unable to send password reset OTP. Verify SMTP settings and try again.' }, 400);
  }
  return c.json({ success: true, maskedEmail: challenge.maskedEmail });
});

app.post('/api/auth/password-reset/verify-otp', async (c) => {
  const body = (await c.req.json<{ otp_code?: string }>().catch(() => ({}))) as { otp_code?: string };
  const otpCode = String(body.otp_code || '').trim();
  const token = getCookie(c, PASSWORD_RESET_COOKIE) || '';
  cleanupExpiredChallengeMap(pendingPasswordResetChallenges);
  const challenge = token ? pendingPasswordResetChallenges.get(token) : null;
  if (!challenge || !isOtpCookieFresh(challenge)) {
    if (token) pendingPasswordResetChallenges.delete(token);
    clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
    return c.json({ error: 'Password reset OTP expired. Start again.' }, 400);
  }
  if (!otpCode || hashOtp(otpCode) !== challenge.otpHash) {
    return c.json({ error: 'Invalid OTP. Please try again.' }, 401);
  }
  pendingPasswordResetChallenges.set(token, { ...challenge, verifiedAt: nowMs() });
  return c.json({ success: true, maskedEmail: maskEmailAddress(challenge.email) });
});

app.post('/api/auth/password-reset/complete', async (c) => {
  const body = (await c.req.json<{ new_password?: string; confirm_password?: string }>().catch(() => ({}))) as {
    new_password?: string;
    confirm_password?: string;
  };
  const newPassword = String(body.new_password || '');
  const confirmPassword = String(body.confirm_password || '');
  if (!newPassword || !confirmPassword) return c.json({ error: 'Both password fields are required.' }, 400);
  if (newPassword !== confirmPassword) return c.json({ error: 'New password and confirm password do not match.' }, 400);
  if (newPassword.length < 6) return c.json({ error: 'Password must be at least 6 characters.' }, 400);

  const token = getCookie(c, PASSWORD_RESET_COOKIE) || '';
  cleanupExpiredChallengeMap(pendingPasswordResetChallenges);
  const challenge = token ? pendingPasswordResetChallenges.get(token) : null;
  if (!challenge || !isOtpCookieFresh(challenge) || !challenge.verifiedAt) {
    if (token && (!challenge || !isOtpCookieFresh(challenge))) pendingPasswordResetChallenges.delete(token);
    clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
    return c.json({ error: 'Verify OTP before resetting the password.' }, 400);
  }
  const userRow = getUserByEmail(challenge.email);
  if (!userRow) {
    pendingPasswordResetChallenges.delete(token);
    clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
    return c.json({ error: 'User not found. Start again.' }, 404);
  }
  updateUserPassword(challenge.email, newPassword);
  forceLogoutUser(challenge.email, 'self_password_reset');
  pendingPasswordResetChallenges.delete(token);
  clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
  return c.json({ success: true });
});

app.post('/api/auth/self-password/send-otp', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  const authUi = getAuthUiConfig(authUser, getAppConfig());
  if (!authUi.selfPasswordOtpEnabled) {
    return c.json({ error: 'OTP is not required for password reset right now.' }, 400);
  }
  try {
    const challenge = await createSelfResetOtpChallenge(c, authUser);
    return c.json({ success: true, maskedEmail: challenge.maskedEmail });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Unable to send OTP.' }, 400);
  }
});

app.post('/api/auth/self-password/update', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  const body = (await c.req.json<{ current_password?: string; otp_code?: string; new_password?: string; confirm_password?: string }>().catch(() => ({}))) as {
    current_password?: string;
    otp_code?: string;
    new_password?: string;
    confirm_password?: string;
  };
  const currentPassword = String(body.current_password || '');
  const otpCode = String(body.otp_code || '').trim();
  const newPassword = String(body.new_password || '');
  const confirmPassword = String(body.confirm_password || '');
  if (!newPassword || !confirmPassword) return c.json({ error: 'Both password fields are required.' }, 400);
  if (newPassword !== confirmPassword) return c.json({ error: 'New password and confirm password do not match.' }, 400);
  if (newPassword.length < 6) return c.json({ error: 'Password must be at least 6 characters.' }, 400);

  const authUi = getAuthUiConfig(authUser, getAppConfig());
  if (authUi.selfPasswordOtpEnabled) {
    const token = getCookie(c, SELF_RESET_OTP_COOKIE) || '';
    cleanupExpiredChallengeMap(pendingSelfResetOtpChallenges);
    const challenge = token ? pendingSelfResetOtpChallenges.get(token) : null;
    if (!challenge || !isOtpCookieFresh(challenge) || challenge.email !== authUser.email) {
      if (token) pendingSelfResetOtpChallenges.delete(token);
      clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
      return c.json({ error: 'Request OTP first before updating password.' }, 400);
    }
    if (!otpCode || hashOtp(otpCode) !== challenge.otpHash) {
      return c.json({ error: 'Invalid OTP.' }, 401);
    }
    pendingSelfResetOtpChallenges.delete(token);
    clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
  } else if (authUi.adminCurrentPasswordFallbackEnabled) {
    const userRow = getUserByEmail(authUser.email);
    if (!userRow || !verifyPassword(currentPassword, String(userRow.password_hash || ''))) {
      return c.json({ error: 'Current password is incorrect.' }, 403);
    }
  }

  updateUserPassword(authUser.email, newPassword);
  return c.json({ success: true });
});

app.get('/api/departments', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  return c.json({ departments: getDepartments(false) });
});

app.post('/api/departments', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const body = (await c.req.json<{ code?: string; name?: string }>().catch(() => ({}))) as {
    code?: string;
    name?: string;
  };

  try {
    const department = createDepartment(body.code || '', body.name || '');
    return c.json({ success: true, department });
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Failed to create department.';
    return c.json({ error: message }, 400);
  }
});

app.put('/api/departments/:id', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const id = Number(c.req.param('id'));
  const body = (await c.req.json<{ code?: string; name?: string }>().catch(() => ({}))) as {
    code?: string;
    name?: string;
  };

  if (!Number.isFinite(id) || id <= 0) {
    return c.json({ error: 'Invalid department id.' }, 400);
  }

  try {
    const department = updateDepartment(id, body.code || '', body.name || '');
    return c.json({ success: true, department });
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Failed to update department.';
    return c.json({ error: message }, 400);
  }
});

app.post('/api/departments/:id/toggle', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const id = Number(c.req.param('id'));
  if (!Number.isFinite(id) || id <= 0) {
    return c.json({ error: 'Invalid department id.' }, 400);
  }

  const department = toggleDepartment(id);
  if (department) {
    const departmentCode = String(department.code || '').trim().toUpperCase();
    if (Number(department.is_active || 0) === 1) {
      unlockCounselorsForDepartment(departmentCode);
    } else {
      lockCounselorsForDepartment(departmentCode);
    }
  }
  return c.json({ success: true, department });
});

app.delete('/api/departments/:id', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const id = Number(c.req.param('id'));
  if (!Number.isFinite(id) || id <= 0) {
    return c.json({ error: 'Invalid department id.' }, 400);
  }

  deleteDepartment(id);
  return c.json({ success: true });
});

app.get('/api/users', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }
  return c.json({
    users: listUsersForActor(authUser).map((item) => mapUserForClient(authUser, item)),
    departments: getDepartments(true),
    actorScopes: authUser.scopes,
    assignableRoles: getAssignableRolesForActor(authUser.role),
  });
});

app.post('/api/users/create', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  const name = String(body.name || '').trim();
  const email = String(body.email || '').trim().toLowerCase();
  const password = String(body.password || '');
  const confirmPassword = String(body.confirm_password || '');
  const role = normalizeUserRole(String(body.role || (authUser.role === 'deo' ? 'counselor' : 'counselor')));
  const department = String(body.department || '').trim().toUpperCase();
  const yearLevel = Number(body.year_level || 1) || 1;
  const maxStudents = Number(body.max_students || 30) || 30;
  const scopePairs = parseScopeValues(Array.isArray(body.scope_pairs) ? body.scope_pairs : []);

  if (!name || !email || !password) return c.json({ error: 'Name, email, and password are required.' }, 400);
  if (password !== confirmPassword) return c.json({ error: 'Password and confirm password do not match.' }, 400);
  if (password.length < 6) return c.json({ error: 'Password must be at least 6 characters.' }, 400);

  if (authUser.role === 'deo' && role !== 'counselor') {
    return c.json({ error: 'DEO can create only counselor accounts.' }, 403);
  }
  if (authUser.role !== 'admin' && ['admin', 'principal', 'hod', 'deo'].includes(role) && role !== 'counselor') {
    return c.json({ error: 'Only system admin can create this role.' }, 403);
  }

  let createDepartmentValue = '';
  let createYearLevel = 1;
  let createMaxStudents = 500;
  let scopePayload = scopePairs;

  if (role === 'admin' || role === 'principal') {
    createDepartmentValue = '';
    createYearLevel = 1;
    createMaxStudents = 500;
    scopePayload = [];
  } else if (role === 'hod' || role === 'deo') {
    if (!scopePayload.length && department && [1, 2, 3, 4].includes(yearLevel)) {
      scopePayload = [{ department, year_level: yearLevel }];
    }
    if (!scopePayload.length) return c.json({ error: 'Assign at least one department/year scope.' }, 400);
    createDepartmentValue = scopePayload[0].department;
    createYearLevel = scopePayload[0].year_level;
    createMaxStudents = 500;
  } else {
    if (!department) return c.json({ error: 'Department is required for counselor accounts.' }, 400);
    if (![1, 2, 3, 4].includes(yearLevel)) return c.json({ error: 'Year must be between 1 and 4.' }, 400);
    if (maxStudents < 1 || maxStudents > 500) return c.json({ error: 'Max students must be between 1 and 500.' }, 400);
    createDepartmentValue = department;
    createYearLevel = yearLevel;
    createMaxStudents = maxStudents;
  }

  if (authUser.role === 'deo') {
    const allowed = new Set(authUser.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
    const targetKey = `${createDepartmentValue}::${createYearLevel}`;
    if (!allowed.has(targetKey)) {
      return c.json({ error: 'You can only create counselors inside your assigned department/year scope.' }, 403);
    }
  }

  if (getUserByEmail(email)) return c.json({ error: 'Email already exists.' }, 409);

  try {
    createUser(email, password, name, role, createDepartmentValue, createMaxStudents, true, createYearLevel);
    if (role === 'hod' || role === 'deo') {
      setChiefAdminScopes(email, scopePayload.length ? scopePayload : [{ department: createDepartmentValue, year_level: createYearLevel }]);
    }
    const defaultAdminDisabled = role === 'admin' ? enforceDefaultAdminDisablePolicy() : false;
    return c.json({ success: true, defaultAdminDisabled });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to create user.' }, 400);
  }
});

app.put('/api/users/:email', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const originalEmail = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(originalEmail);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'edit')) return c.json({ error: 'You do not have permission to edit this user.' }, 403);

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  const updates: Record<string, unknown> = {};
  const requestedName = String(body.name || '').trim();
  const requestedEmail = String(body.email || '').trim().toLowerCase();
  const requestedPassword = String(body.password || '');
  let requestedRole = normalizeUserRole(String(body.role || target.role || 'counselor'));
  let requestedDepartment = String(body.department || target.department || '').trim().toUpperCase();
  let requestedYear = Number(body.year_level || target.year_level || 1) || 1;
  let requestedMaxStudents = Number(body.max_students || target.max_students || 30) || 30;
  let requestedScopes = parseScopeValues(Array.isArray(body.scope_pairs) ? body.scope_pairs : []);

  if (requestedName) updates.name = requestedName;
  if (requestedPassword) {
    if (requestedPassword.length < 6) return c.json({ error: 'Password must be at least 6 characters.' }, 400);
    updates.password = requestedPassword;
  }

  if (authUser.role !== 'admin') {
    requestedRole = normalizeUserRole(String(target.role || 'counselor'));
  } else {
    updates.role = requestedRole;
  }

  if (requestedEmail && requestedEmail !== originalEmail) {
    const existing = getUserByEmail(requestedEmail);
    if (existing && String(existing.email || '').trim().toLowerCase() !== originalEmail) {
      return c.json({ error: 'Email already exists.' }, 409);
    }
  }

  if (requestedRole === 'admin' || requestedRole === 'principal') {
    updates.department = '';
    updates.year_level = 1;
    updates.max_students = 500;
    requestedScopes = [];
  } else if (requestedRole === 'hod' || requestedRole === 'deo') {
    if (!requestedScopes.length && requestedDepartment && [1, 2, 3, 4].includes(requestedYear)) {
      requestedScopes = [{ department: requestedDepartment, year_level: requestedYear }];
    }
    if (!requestedScopes.length) return c.json({ error: 'Assign at least one department/year scope.' }, 400);
    updates.department = requestedScopes[0].department;
    updates.year_level = requestedScopes[0].year_level;
    updates.max_students = 500;
    requestedDepartment = requestedScopes[0].department;
    requestedYear = requestedScopes[0].year_level;
  } else {
    if (!requestedDepartment) return c.json({ error: 'Department is required for counselor accounts.' }, 400);
    if (![1, 2, 3, 4].includes(requestedYear)) return c.json({ error: 'Year must be between 1 and 4.' }, 400);
    if (requestedMaxStudents < 1 || requestedMaxStudents > 500) return c.json({ error: 'Max students must be between 1 and 500.' }, 400);
    updates.department = requestedDepartment;
    updates.year_level = requestedYear;
    updates.max_students = requestedMaxStudents;
  }

  if (authUser.role === 'deo') {
    const allowed = new Set(authUser.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
    if (!allowed.has(`${requestedDepartment}::${requestedYear}`)) {
      return c.json({ error: 'Update rejected: target department/year is outside your assigned scope.' }, 403);
    }
  }

  try {
    let effectiveEmail = originalEmail;
    if (requestedEmail && requestedEmail !== originalEmail) {
      renameUserEmail(originalEmail, requestedEmail);
      effectiveEmail = requestedEmail;
    }
    updateUser(effectiveEmail, updates);
    if (authUser.role === 'admin') {
      if (requestedRole === 'hod' || requestedRole === 'deo') {
        setChiefAdminScopes(effectiveEmail, requestedScopes.length ? requestedScopes : [{ department: requestedDepartment, year_level: requestedYear }]);
      } else {
        setChiefAdminScopes(effectiveEmail, []);
      }
      if (requestedRole === 'admin') {
        enforceDefaultAdminDisablePolicy();
      }
    }
    return c.json({ success: true });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to update user.' }, 400);
  }
});

app.post('/api/users/:email/lock', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'manage')) return c.json({ error: 'You do not have permission to lock this user.' }, 403);

  lockUser(email);
  return c.json({ success: true });
});

app.post('/api/users/:email/unlock', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'manage')) return c.json({ error: 'You do not have permission to unlock this user.' }, 403);

  unlockUser(email);
  return c.json({ success: true });
});

app.delete('/api/users/:email', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'manage')) return c.json({ error: 'You do not have permission to delete this user.' }, 403);

  deleteUser(email);
  return c.json({ success: true });
});

app.post('/api/users/bulk-counselors-upload', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const form = await c.req.formData();
  const file = form.get('file');
  const yearLevel = Number(form.get('year_level') || 1) || 1;
  if (![1, 2, 3, 4].includes(yearLevel)) return c.json({ error: 'Year must be between 1 and 4.' }, 400);
  if (!(file instanceof File)) return c.json({ error: 'Upload an Excel file first.' }, 400);

  const appConfig = getAppConfig();
  const bulkPasswordMode = String(appConfig.google_oauth_bulk_password_mode || 'sheet').trim().toLowerCase() === 'override' ? 'override' : 'sheet';
  const configuredOverridePassword = String(appConfig.google_oauth_bulk_override_password || '').trim();
  const oauthEnabled = String(appConfig.google_oauth_enabled || 'false').trim().toLowerCase() === 'true';
  const activeDepartments = getDepartments(true);
  const allowedDepartmentCodes = authUser.role === 'deo'
    ? Array.from(new Set(authUser.scopes.map((scope) => scope.department.toUpperCase())))
    : activeDepartments.map((department) => department.code.toUpperCase());

  let rows: ReturnType<typeof parseBulkCounselorWorkbook> = [];
  try {
    const bytes = await file.arrayBuffer();
    rows = parseBulkCounselorWorkbook(Buffer.from(bytes), allowedDepartmentCodes);
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Could not parse counselor file.' }, 400);
  }

  if (!rows.length) return c.json({ error: 'No valid counselor rows found in the uploaded file.' }, 400);

  let created = 0;
  let updated = 0;
  let skipped = 0;
  let locked = 0;

  for (const item of rows) {
    if (authUser.role === 'deo') {
      const allowed = new Set(authUser.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
      if (!allowed.has(`${item.department}::${yearLevel}`)) {
        skipped += 1;
        continue;
      }
    }

    const existing = getUserByEmail(item.email);
    const selectedPassword = oauthEnabled
      ? (bulkPasswordMode === 'override' ? configuredOverridePassword : item.password)
      : (configuredOverridePassword || item.password);
    const hasValidPassword = selectedPassword.length >= 6;
    const shouldLock = item.needs_lock || !hasValidPassword;

    if (!existing) {
      try {
        createUser(
          item.email,
          hasValidPassword ? selectedPassword : 'temp1234',
          item.name || item.email.split('@')[0],
          'counselor',
          item.department,
          30,
          true,
          yearLevel,
        );
        if (shouldLock) {
          lockUser(item.email, `Locked after bulk upload. Missing: ${(item.missing_required || []).join(', ') || 'valid password'}`);
          locked += 1;
        }
        created += 1;
      } catch {
        skipped += 1;
      }
      continue;
    }

    if (normalizeUserRole(String(existing.role || 'counselor')) !== 'counselor') {
      skipped += 1;
      continue;
    }

    const payload: Record<string, unknown> = {
      name: item.name || String(existing.name || item.email),
      role: 'counselor',
      department: item.department,
      year_level: yearLevel,
      max_students: 30,
    };
    if (hasValidPassword) payload.password = selectedPassword;
    updateUser(item.email, payload);
    if (shouldLock) {
      lockUser(item.email, `Locked after bulk upload. Missing: ${(item.missing_required || []).join(', ') || 'valid password'}`);
      locked += 1;
    } else {
      unlockUser(item.email);
    }
    updated += 1;
  }

  return c.json({
    success: true,
    message: `Bulk counselor sync completed. Created: ${created}, Updated: ${updated}, Skipped: ${skipped}${locked ? `. Locked: ${locked}.` : '.'}`,
  });
});

app.get('/api/users/:email/students', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (normalizeUserRole(String(target.role || 'counselor')) !== 'counselor') return c.json({ error: 'Student lists are available only for counselor accounts.' }, 400);
  if (authUser.role !== 'principal' && !actorCanManageUser(authUser, target, 'edit') && authUser.role !== 'admin') {
    return c.json({ error: 'You do not have permission to access this student list.' }, 403);
  }
  return c.json({ students: getStudentsForCounselor(email) });
});

app.post('/api/users/:email/students/upload', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'edit')) return c.json({ error: 'You do not have permission to upload students for this user.' }, 403);

  const form = await c.req.formData();
  const file = form.get('student_file');
  if (!(file instanceof File)) return c.json({ error: 'No file selected.' }, 400);

  const bytes = await file.arrayBuffer();
  const students = parseStudentWorkbook(Buffer.from(bytes));
  if (!students.length) return c.json({ error: 'No valid students found.' }, 400);
  const added = addStudentsBulk(email, students);
  return c.json({ success: true, count: added });
});

app.post('/api/users/:email/students/save', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'edit')) return c.json({ error: 'You do not have permission to manage students for this user.' }, 403);

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  try {
    saveCounselorStudent(email, {
      reg_no: String(body.reg_no || ''),
      student_name: String(body.student_name || ''),
      parent_phone: String(body.parent_phone || ''),
      parent_email: String(body.parent_email || ''),
      department: String(body.department || target.department || ''),
    });
    return c.json({ success: true });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to save student.' }, 400);
  }
});

app.delete('/api/users/:email/students/:regNo', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const regNo = decodeURIComponent(String(c.req.param('regNo') || '')).trim();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'edit')) return c.json({ error: 'You do not have permission to manage students for this user.' }, 403);

  deleteCounselorStudent(email, regNo);
  return c.json({ success: true });
});

app.delete('/api/users/:email/students', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) return c.json({ error: 'Forbidden' }, 403);

  const email = decodeURIComponent(String(c.req.param('email') || '')).trim().toLowerCase();
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'User not found.' }, 404);
  if (!actorCanManageUser(authUser, target, 'edit')) return c.json({ error: 'You do not have permission to manage students for this user.' }, 403);

  deleteAllCounselorStudents(email);
  return c.json({ success: true });
});

app.get('/api/reports/overview', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal' || authUser.role === 'hod' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const filterDept = String(c.req.query('department') || '').trim().toUpperCase();
  const filterYearLevel = Number(c.req.query('year') || 0) || null;
  const allowedScopes = getAllowedScopesForUser(authUser);
  const allDepartments = getDepartments(true);

  const visibleDepartments = allowedScopes
    ? allDepartments.filter((department) =>
        authUser.scopes.some((scope) => scope.department.toUpperCase() === department.code.toUpperCase()),
      )
    : allDepartments;

  const yearsByDepartment = new Map<string, number[]>();
  if (allowedScopes) {
    for (const scope of authUser.scopes) {
      const key = scope.department.toUpperCase();
      if (!yearsByDepartment.has(key)) yearsByDepartment.set(key, []);
      yearsByDepartment.get(key)!.push(scope.year_level);
    }
  } else {
    for (const department of visibleDepartments) {
      yearsByDepartment.set(department.code.toUpperCase(), [1, 2, 3, 4]);
    }
  }

  const resolvedDepartment =
    filterDept && visibleDepartments.some((department) => department.code.toUpperCase() === filterDept)
      ? filterDept
      : (visibleDepartments.length === 1 ? visibleDepartments[0].code.toUpperCase() : '');

  const availableYears = resolvedDepartment
    ? Array.from(new Set((yearsByDepartment.get(resolvedDepartment) || []).filter((year) => year >= 1 && year <= 4))).sort((a, b) => a - b)
    : [];

  const selectedYear = filterYearLevel && availableYears.includes(filterYearLevel)
    ? filterYearLevel
    : (availableYears.length === 1 ? availableYears[0] : null);
  const tests =
    resolvedDepartment && selectedYear
      ? getAllUniqueTests({
          filterDept: resolvedDepartment,
          filterYearLevel: selectedYear,
          allowedScopes,
        })
      : [];

  return c.json({
    departments: visibleDepartments,
    selectedDepartment: resolvedDepartment,
    availableYears,
    selectedYear,
    tests,
  });
});

app.get('/api/counselor/overview', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role !== 'counselor') return c.json({ error: 'Forbidden' }, 403);

  return c.json(buildCounselorOverviewPayload(authUser.email));
});

app.get('/api/counselor/tests', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role !== 'counselor') return c.json({ error: 'Forbidden' }, 403);
  return c.json({ tests: getVisibleTestsForCounselor(authUser.email) });
});

app.get('/api/counselor/tests/:id/send', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role !== 'counselor') return c.json({ error: 'Forbidden' }, 403);

  const testId = Number(c.req.param('id'));
  if (!Number.isFinite(testId) || testId <= 0) return c.json({ error: 'Invalid test id.' }, 400);
  if (!canCounselorAccessTest(testId, authUser.email)) {
    return c.json({ error: 'Access denied for this test.' }, 403);
  }

  const meta = getTestMetadata(testId);
  if (!meta) return c.json({ error: 'Test not found.' }, 404);
  if (Boolean(Number(meta.is_blocked || 0))) {
    return c.json({ error: 'This test is blocked by administration. Sending is disabled.' }, 403);
  }

  const requestedMode = String(c.req.query('mode') || 'app').trim().toLowerCase();
  const sendMode = requestedMode === 'web' ? 'web' : 'app';
  const appConfig = getAppConfig();
  return c.json({
    testId,
    meta: {
      test_name: String(meta.test_name || ''),
      semester: String(meta.semester || ''),
      department: String(meta.department || ''),
      year_level: Number(meta.year_level || 1),
      section: String(meta.section || ''),
      batch_name: String(meta.batch_name || ''),
      is_blocked: Number(meta.is_blocked || 0),
    },
    rows: getCounselorSendReportRows(testId, authUser.email),
    defaultBatchName: getBatchNameForYearLevel(Number(meta.year_level || 1), appConfig),
    sendMode,
    batchSendEnabled: String(appConfig.enable_counselor_batch_send || 'true').toLowerCase() === 'true' && sendMode === 'app',
    batchSendDelaySeconds: Number(appConfig.counselor_batch_send_delay_seconds || 4) || 4,
  });
});

app.get('/api/counselor/messages', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role !== 'counselor') return c.json({ error: 'Forbidden' }, 403);
  return c.json({
    stats: getCounselorMessageStats(authUser.email),
    messages: getCounselorMessageHistory(authUser.email, 50),
  });
});

app.post('/api/reports/upload', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const form = await c.req.formData();
  const rawFile = form.get('marks_file');
  if (!rawFile || typeof rawFile === 'string' || typeof (rawFile as { arrayBuffer?: unknown }).arrayBuffer !== 'function') {
    return c.json({ error: 'No marks file selected.' }, 400);
  }

  const department = String(form.get('department') || '').trim().toUpperCase();
  const yearLevel = Number(form.get('year_level') || 0) || 1;
  const semester = String(form.get('semester') || '').trim();
  const batchNameInput = String(form.get('batch_name') || '').trim();
  const section = String(form.get('section') || '').trim();
  const testNameInput = String(form.get('test_name') || '').trim();
  const uploadMode = String(form.get('upload_mode') || 'new').trim().toLowerCase() === 'replace' ? 'replace' : 'new';

  if (!department || ![1, 2, 3, 4].includes(yearLevel) || !semester) {
    return c.json({ error: 'Department, year and semester are required.' }, 400);
  }

  if (!canManageDepartmentYear(authUser, department, yearLevel)) {
    return c.json({ error: 'You can upload tests only in your assigned department/year scope.' }, 403);
  }

  try {
    const file = rawFile as { name: string; arrayBuffer(): Promise<ArrayBuffer> };
    const fileBytes = Buffer.from(await file.arrayBuffer());
    const fileHash = createHash('sha256').update(fileBytes).digest('hex');
    const parsed = await parseUploadedMarksheet(file.name, fileBytes);

    if (!parsed.students.length) {
      return c.json({ error: 'No student marks data found in file.' }, 400);
    }

    const subjects = (parsed.testInfo.subjects || []).map((subject) => String(subject.name || '').trim()).filter(Boolean);
    if (!subjects.length) {
      return c.json({ error: 'Upload blocked: no subject columns detected.' }, 400);
    }

    const testName = normalizeAllowedTestName(testNameInput || parsed.testInfo.test_name || '');
    if (!testName) {
      return c.json({ error: 'Test name must be one of: IAT 1, IAT 2, MODEL EXAM.' }, 400);
    }

    const appConfig = getAppConfig();
    const batchName = batchNameInput || getBatchNameForYearLevel(yearLevel, appConfig);
    const existing = findExistingDepartmentYearTest(department, yearLevel, semester, testName, batchName);

    if (existing && String(existing.file_hash || '') === fileHash) {
      return c.json({ error: 'Duplicate file detected for this department/year/test. Upload blocked.' }, 409);
    }

    const replaceTestId = existing && uploadMode === 'replace' ? Number(existing.test_id) : null;
    const result = saveUploadedTestMarks({
      test_name: testName,
      semester,
      counselor_email: authUser.email,
      students: parsed.students,
      subjects,
      batch_name: batchName,
      department,
      section,
      file_hash: fileHash,
      replace_test_id: replaceTestId,
      year_level: yearLevel,
      uploaded_by: authUser.email,
    });

    return c.json({
      success: true,
      message: `Marksheet uploaded for ${department} Year ${yearLevel} (${parsed.students.length} students).`,
      testId: result.testId,
      studentCount: parsed.students.length,
      parserWarnings: parsed.errors,
    });
  } catch (error) {
    const message = error instanceof Error ? error.message : 'Upload failed.';
    return c.json({ error: `Upload failed: ${message}` }, 400);
  }
});

app.post('/api/reports/send-single', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role !== 'counselor') return c.json({ error: 'Forbidden' }, 403);

  const form = await c.req.formData();
  const testId = Number(form.get('test_id') || 0);
  const regNoRaw = String(form.get('reg_no') || '').trim();
  const action = String(form.get('action') || 'cancel').trim().toLowerCase();
  const step = String(form.get('step') || 'send').trim().toLowerCase();
  const orderedFieldsRaw = String(form.get('ordered_fields') || '').trim();

  let orderedFields: Array<{ type?: string; raw_key?: string; normalized_key?: string; key?: string }> | undefined;
  if (orderedFieldsRaw) {
    try {
      const parsed = JSON.parse(orderedFieldsRaw);
      if (Array.isArray(parsed)) orderedFields = parsed;
    } catch {
      orderedFields = undefined;
    }
  }

  if (!testId || !regNoRaw) {
    return c.json({ error: 'Test and student are required.' }, 400);
  }
  if (!canCounselorAccessTest(testId, authUser.email)) {
    return c.json({ error: 'Access denied for this test.' }, 403);
  }

  const testMeta = getTestMetadata(testId) || null;
  if (!testMeta) return c.json({ error: 'Test not found.' }, 404);
  if (Boolean(Number(testMeta.is_blocked || 0))) {
    return c.json({ error: 'Test is blocked.' }, 403);
  }

  if (action !== 'send') {
    return c.json({ success: true, status: 'pending' });
  }

  const students = getStudentsForCounselor(authUser.email);
  const normalizedReg = normalizeRegNo(regNoRaw);
  const student = students.find((item) => normalizeRegNo(item.reg_no) === normalizedReg) || null;
  if (!student) {
    return c.json({ error: 'Student not found under your account.' }, 404);
  }

  if (step === 'confirm') {
    const deliveryToken = String(form.get('delivery_token') || '').trim();
    const deliveryOutcome = String(form.get('delivery_outcome') || 'sent').trim().toLowerCase();
    const receipt = getSendReceipt(deliveryToken);

    if (!receipt) {
      if (deliveryOutcome === 'sent' && getSentRegNosForTest(authUser.email, testId).has(normalizedReg)) {
        return c.json({ success: true, status: 'generated', reg_no: normalizedReg });
      }
      return c.json({ error: 'Delivery session expired. Please start again.' }, 400);
    }
    if (String(receipt.email || '').trim().toLowerCase() !== authUser.email.toLowerCase()) {
      return c.json({ error: 'Delivery token does not belong to this user.' }, 403);
    }
    if (Number(receipt.test_id || 0) !== testId) {
      return c.json({ error: 'Delivery token does not match this test.' }, 400);
    }
    if (normalizeRegNo(receipt.reg_no) !== normalizedReg) {
      return c.json({ error: 'Delivery token does not match this student.' }, 400);
    }

    if (deliveryOutcome === 'sent') {
      logMessage(
        authUser.email,
        normalizedReg,
        student.student_name || '',
        String(receipt.message || '').trim() || 'Message content unavailable',
        'message',
        String(receipt.wa_link || ''),
        {
          test_id: testId,
          status: 'sent',
          delivery_status: 'confirmed',
          send_mode: String(receipt.send_mode || 'app').trim(),
        },
      );
      deleteSendReceipt(deliveryToken);
      return c.json({ success: true, status: 'generated', reg_no: normalizedReg });
    }

    deleteSendReceipt(deliveryToken);
    return c.json({ success: true, status: deliveryOutcome === 'failed' ? 'failed' : 'skipped', reg_no: normalizedReg });
  }

  const marks = getStudentMarksForRegForCounselor(testId, normalizedReg, authUser.email);
  if (!Object.keys(marks).length) {
    return c.json({ error: 'No marks found for selected student.' }, 400);
  }

  const template = String(form.get('message_template') || '').trim();
  const effectiveTestName = String(form.get('test_name') || testMeta.test_name || 'Unit Test').trim();
  const department = String(form.get('department') || testMeta.department || student.department || '').trim();
  const semester = String(form.get('semester') || testMeta.semester || '-').trim();
  const batchName = String(form.get('batch_name') || testMeta.batch_name || '-').trim();
  const section = String(form.get('section') || testMeta.section || '-').trim();
  const subjectsTable = buildParentSubjectsTable(marks, orderedFields);
  const userRow = getUserByEmail(authUser.email) || null;
  const message = template
    ? fillTemplate(template, {
        app_name: 'RMKCET SHINE',
        reg_no: normalizedReg,
        student_name: student.student_name || normalizedReg,
        department,
        test_name: effectiveTestName,
        semester,
        batch_name: batchName,
        section,
        subjects_table: subjectsTable,
        counselor_name: String(userRow?.name || 'Counselor'),
      })
    : buildParentMessage(effectiveTestName, normalizedReg, student.student_name || normalizedReg, marks);

  let phone = normalizePhone(student.parent_phone);
  if (!phone) {
    phone = normalizePhone(student.parent_email);
  }
  if (!phone) {
    for (const candidate of students) {
      if (normalizeRegNo(candidate.reg_no) !== normalizedReg) continue;
      phone = normalizePhone(candidate.parent_phone) || normalizePhone(candidate.parent_email);
      if (phone) break;
    }
  }
  if (!phone) {
    return c.json({ error: `Parent phone number missing for ${normalizedReg}.` }, 400);
  }

  const waLink = getWhatsappLink(phone, message);
  const requestSendMode = String(form.get('send_mode') || 'app').trim().toLowerCase() === 'web' ? 'web' : 'app';

  if (step === 'prepare') {
    const deliveryToken = createSendReceipt({
      kind: 'report',
      email: authUser.email,
      test_id: testId,
      reg_no: normalizedReg,
      student_name: student.student_name || '',
      message,
      wa_link: waLink,
      send_mode: requestSendMode,
    });
    return c.json({
      success: true,
      status: 'prepared',
      reg_no: normalizedReg,
      wa_link: waLink,
      delivery_token: deliveryToken,
    });
  }

  logMessage(authUser.email, normalizedReg, student.student_name || '', message, 'message', waLink, {
    test_id: testId,
    send_mode: requestSendMode,
  });
  return c.json({ success: true, status: 'generated', wa_link: waLink });
});

app.get('/api/tests/:id/detail', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal' || authUser.role === 'hod' || authUser.role === 'deo' || authUser.role === 'counselor')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const testId = Number(c.req.param('id'));
  if (!Number.isFinite(testId) || testId <= 0) {
    return c.json({ error: 'Invalid test id.' }, 400);
  }

  const meta = getTestMetadata(testId);
  if (!meta) return c.json({ error: 'Test not found.' }, 404);
  const department = String(meta.department || '').trim().toUpperCase();
  const yearLevel = Number(meta.year_level || 1);
  if (authUser.role === 'counselor') {
    if (!canCounselorAccessTest(testId, authUser.email)) {
      return c.json({ error: 'Access denied for this test.' }, 403);
    }
  } else if (!canManageDepartmentYear(authUser, department, yearLevel)) {
    return c.json({ error: 'Access denied for this test.' }, 403);
  }

  const grouped = authUser.role === 'counselor' ? getTestMarksGroupedForCounselor(testId, authUser.email) : getTestMarksGrouped(testId);
  return c.json({
    testId,
    meta: {
      ...meta,
      department,
      year_level: yearLevel,
    },
    subjects: getVisibleReportSubjects(grouped.subjects || []),
    students: grouped.students || [],
    isReadOnly: authUser.role === 'principal' || authUser.role === 'counselor',
    isMetaReadOnly: authUser.role === 'principal' || authUser.role === 'counselor',
    isMarksReadOnly: authUser.role === 'principal',
  });
});

app.put('/api/tests/:id/meta', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role === 'principal') return c.json({ error: 'Principal is read-only.' }, 403);
  if (!(authUser.role === 'admin' || authUser.role === 'hod' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const testId = Number(c.req.param('id'));
  const meta = getTestMetadata(testId);
  if (!meta) return c.json({ error: 'Test not found.' }, 404);
  const department = String(meta.department || '').trim().toUpperCase();
  const yearLevel = Number(meta.year_level || 1);
  if (!canManageDepartmentYear(authUser, department, yearLevel)) {
    return c.json({ error: 'Access denied for this test.' }, 403);
  }

  const body = (await c.req.json<{
    test_name?: string;
    semester?: string;
    batch_name?: string;
    section?: string;
  }>().catch(() => ({}))) as {
    test_name?: string;
    semester?: string;
    batch_name?: string;
    section?: string;
  };

  const allowedNames = new Set(['IAT 1', 'IAT 2', 'MODEL EXAM']);
  const testName = String(body.test_name || meta.test_name || '').trim().toUpperCase();
  if (!allowedNames.has(testName)) {
    return c.json({ error: 'Test name must be one of: IAT 1, IAT 2, MODEL EXAM.' }, 400);
  }

  updateTestMetadataFields(testId, {
    test_name: testName,
    semester: String(body.semester || meta.semester || '').trim(),
    department,
    batch_name: String(body.batch_name || meta.batch_name || '').trim(),
    section: String(body.section || meta.section || '').trim(),
  });

  return c.json({ success: true });
});

app.post('/api/tests/:id/marks/update', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role === 'principal') return c.json({ error: 'Principal is read-only.' }, 403);
  if (!(authUser.role === 'admin' || authUser.role === 'hod' || authUser.role === 'deo' || authUser.role === 'counselor')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const testId = Number(c.req.param('id'));
  const meta = getTestMetadata(testId);
  if (!meta) return c.json({ error: 'Test not found.' }, 404);
  const department = String(meta.department || '').trim().toUpperCase();
  const yearLevel = Number(meta.year_level || 1);
  if (authUser.role === 'counselor') {
    if (!canCounselorAccessTest(testId, authUser.email)) {
      return c.json({ error: 'Access denied for this test.' }, 403);
    }
  } else if (!canManageDepartmentYear(authUser, department, yearLevel)) {
    return c.json({ error: 'Access denied for this test.' }, 403);
  }

  const body = (await c.req.json<{ reg_no?: string; marks?: Record<string, string> }>().catch(() => ({}))) as {
    reg_no?: string;
    marks?: Record<string, string>;
  };
  const regNo = String(body.reg_no || '').trim();
  const marks = body.marks || {};
  if (!regNo || typeof marks !== 'object') {
    return c.json({ error: 'Invalid payload.' }, 400);
  }

  for (const [subject, value] of Object.entries(marks)) {
    if (!String(subject || '').trim()) continue;
    if (authUser.role === 'counselor') {
      if (!canCounselorAccessStudent(testId, authUser.email, regNo)) {
        return c.json({ error: 'Access denied for this student.' }, 403);
      }
      upsertCounselorMarkOverride(authUser.email, testId, regNo, subject, String(value ?? ''));
    } else {
      upsertTestMark(testId, regNo, subject, String(value ?? ''), department, authUser.email);
    }
  }
  return c.json({ success: true });
});

app.post('/api/tests/:id/toggle-block', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal' || authUser.role === 'hod' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const testId = Number(c.req.param('id'));
  const meta = getTestMetadata(testId);
  if (!meta) return c.json({ error: 'Test not found.' }, 404);
  const department = String(meta.department || '').trim().toUpperCase();
  const yearLevel = Number(meta.year_level || 1);
  if (!canManageDepartmentYear(authUser, department, yearLevel)) {
    return c.json({ error: 'Access denied for this test.' }, 403);
  }

  const nextValue = !Boolean(Number(meta.is_blocked || 0));
  updateTestBlockStatus(testId, nextValue);
  return c.json({ success: true, is_blocked: nextValue ? 1 : 0 });
});

app.delete('/api/tests/:id', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role === 'principal') return c.json({ error: 'Principal is read-only.' }, 403);
  if (!(authUser.role === 'admin' || authUser.role === 'hod' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const testId = Number(c.req.param('id'));
  const meta = getTestMetadata(testId);
  if (!meta) return c.json({ error: 'Test not found.' }, 404);
  const department = String(meta.department || '').trim().toUpperCase();
  const yearLevel = Number(meta.year_level || 1);
  if (!canManageDepartmentYear(authUser, department, yearLevel)) {
    return c.json({ error: 'Access denied for this test.' }, 403);
  }

  deleteTest(testId);
  return c.json({ success: true });
});

app.get('/api/notices/overview', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);

  const filterDepartment = String(c.req.query('department') || '').trim().toUpperCase();
  const filterYearLevel = Number(c.req.query('year') || 0) || null;
  const filterStatus = String(c.req.query('status') || '').trim().toLowerCase() || null;
  const filterDateFrom = String(c.req.query('date_from') || '').trim() || null;
  const filterDateTo = String(c.req.query('date_to') || '').trim() || null;
  const editId = Number(c.req.query('edit_id') || 0) || null;

  const allDepartments = getDepartments(true);
  const visibleDepartments =
    authUser.role === 'admin' || authUser.role === 'principal'
      ? allDepartments
      : authUser.role === 'hod' || authUser.role === 'deo'
        ? allDepartments.filter((department) =>
            authUser.scopes.some((scope) => scope.department.toUpperCase() === department.code.toUpperCase()),
          )
        : allDepartments.filter((department) => department.code.toUpperCase() === String(authUser.department || '').trim().toUpperCase());

  if (authUser.role === 'counselor') {
    return c.json({
      departments: visibleDepartments,
      availableYears: [Number(authUser.year_level || 1)],
      records: getVisibleNoticesForCounselor(authUser.email, {
        filterStatus,
        filterDateFrom,
        filterDateTo,
      }),
      completionRows: [],
      editNotice: null,
      filters: {
        department: '',
        year: null,
        status: filterStatus || '',
        date_from: filterDateFrom || '',
        date_to: filterDateTo || '',
      },
    });
  }

  const records = getNoticeRecordsForActor(authUser, {
    filterDepartment,
    filterYearLevel,
    filterStatus,
    filterDateFrom,
    filterDateTo,
  });
  const completionRows = getNoticeCompletionRows(authUser);
  const availableYears = Array.from(
    new Set(
      (authUser.role === 'admin' || authUser.role === 'principal'
        ? [1, 2, 3, 4]
        : authUser.scopes.map((scope) => scope.year_level)
      ).filter((year) => [1, 2, 3, 4].includes(Number(year))),
    ),
  ).sort((a, b) => a - b);

  const editNotice = editId
    ? (getNoticeRecordsForActor(authUser).find((record) => record.id === editId && record.can_manage_fully) || null)
    : null;

  return c.json({
    departments: visibleDepartments,
    availableYears,
    records,
    completionRows,
    editNotice,
    filters: {
      department: filterDepartment,
      year: filterYearLevel,
      status: filterStatus || '',
      date_from: filterDateFrom || '',
      date_to: filterDateTo || '',
    },
  });
});

app.get('/api/counselor/notices/:id/send', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role !== 'counselor') return c.json({ error: 'Forbidden' }, 403);

  const noticeId = Number(c.req.param('id'));
  if (!Number.isFinite(noticeId) || noticeId <= 0) {
    return c.json({ error: 'Invalid notice id.' }, 400);
  }
  if (!canCounselorAccessNotice(noticeId, authUser.email)) {
    return c.json({ error: 'Access denied for this notice.' }, 403);
  }

  const notice = getNotice(noticeId);
  if (!notice) return c.json({ error: 'Notice not found.' }, 404);

  const sendMode = String(c.req.query('mode') || 'app').trim().toLowerCase() === 'web' ? 'web' : 'app';
  const attachments = getNoticeAttachments(noticeId);
  const attachmentLinksText = buildNoticeAttachmentLinksText(c, attachments);
  const appConfig = getAppConfig();

  return c.json({
    noticeId,
    notice: {
      title: String(notice.title || '').trim(),
      message_text: String(notice.message_text || '').trim(),
      title_display: String(notice.title || '').trim() || 'Selected Notice',
    },
    rows: getCounselorSendNoticeRows(noticeId, authUser.email),
    attachments,
    defaultTemplate: buildDefaultNoticeMessage(String(notice.title || ''), String(notice.message_text || ''), attachmentLinksText),
    attachmentLinksText,
    sendMode,
    batchSendEnabled: String(appConfig.enable_counselor_batch_send || 'true').toLowerCase() === 'true',
    batchSendDelaySeconds: Math.max(1, Number(appConfig.counselor_batch_send_delay_seconds || 4) || 4),
  });
});

app.post('/api/notices/save', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const form = await c.req.formData();
  const noticeId = Number(form.get('notice_id') || 0) || null;
  const title = String(form.get('notice_title') || '').trim();
  const messageText = String(form.get('notice_message_text') || '').trim();
  const sendToAllRequested = String(form.get('notice_send_to_all') || '') === 'on';
  const removeAttachmentIds = form
    .getAll('remove_attachment_ids')
    .map((value) => Number(value || 0) || 0)
    .filter((value) => value > 0);
  let scopePairs = parseNoticeScopeValues(form.getAll('notice_scope_pairs'));

  if (authUser.role === 'hod' || authUser.role === 'deo') {
    if (sendToAllRequested || !scopePairs.length) {
      scopePairs = authUser.scopes.map((scope) => ({ department: scope.department, year_level: scope.year_level }));
    } else {
      scopePairs = scopePairs.filter((scope) => canManageDepartmentYear(authUser, scope.department, scope.year_level));
    }
  }

  const sendToAll = (authUser.role === 'admin' || authUser.role === 'principal') && sendToAllRequested;
  const uploads = form
    .getAll('notice_attachments')
    .filter((item): item is File => item instanceof File && item.size > 0);

  if (!title && !messageText && !uploads.length && !noticeId) {
    return c.json({ error: 'Enter notice text/title or add at least one attachment.' }, 400);
  }
  if (!sendToAll && !scopePairs.length) {
    return c.json({ error: 'Choose at least one department/year scope for this notice.' }, 400);
  }

  let targetNoticeId = noticeId;
  if (targetNoticeId) {
    if (!canFullyManageNotice(authUser, targetNoticeId)) {
      return c.json({ error: 'You do not have permission to edit this notice.' }, 403);
    }
    updateNotice(targetNoticeId, title, messageText, sendToAll, scopePairs);
  } else {
    targetNoticeId = createNotice(title, messageText, sendToAll, authUser.email, authUser.role, scopePairs);
  }

  for (const attachmentId of removeAttachmentIds) {
    const removed = deleteNoticeAttachment(attachmentId);
    if (!removed) continue;
    try {
      await unlink(resolve(NOTICE_UPLOAD_ROOT, removed.relative_path));
    } catch {
      // Ignore missing files.
    }
  }

  if (uploads.length) {
    const targetDir = resolve(NOTICE_UPLOAD_ROOT, `notice_${targetNoticeId}`);
    await mkdir(targetDir, { recursive: true });

    for (const file of uploads) {
      const extension = extname(file.name || '').slice(0, 12);
      const storedName = `${randomUUID().replace(/-/g, '')}${extension}`;
      const originalName = sanitizeFileName(file.name || storedName);
      const relativePath = `notice_${targetNoticeId}/${storedName}`;
      const absolutePath = resolve(NOTICE_UPLOAD_ROOT, relativePath);
      await mkdir(dirname(absolutePath), { recursive: true });
      const bytes = Buffer.from(await file.arrayBuffer());
      await writeFile(absolutePath, bytes);
      addNoticeAttachment(targetNoticeId, storedName, originalName, relativePath, file.type || '', bytes.length);
    }
  }

  return c.json({ success: true, noticeId: targetNoticeId });
});

app.delete('/api/notices/:id', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const noticeId = Number(c.req.param('id'));
  if (!Number.isFinite(noticeId) || noticeId <= 0) return c.json({ error: 'Invalid notice id.' }, 400);
  if (!canFullyManageNotice(authUser, noticeId)) return c.json({ error: 'You do not have permission to delete this notice.' }, 403);

  const attachments = deleteNotice(noticeId);
  for (const attachment of attachments) {
    try {
      await unlink(resolve(NOTICE_UPLOAD_ROOT, attachment.relative_path));
    } catch {
      // Ignore missing files.
    }
  }
  try {
    await rm(resolve(NOTICE_UPLOAD_ROOT, `notice_${noticeId}`), { recursive: true, force: true });
  } catch {
    // Ignore missing directories.
  }
  return c.json({ success: true });
});

app.post('/api/notices/send-single', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role !== 'counselor') return c.json({ error: 'Forbidden' }, 403);

  const form = await c.req.formData();
  const noticeId = Number(form.get('notice_id') || 0);
  const regNoRaw = String(form.get('reg_no') || '').trim();
  const action = String(form.get('action') || 'cancel').trim().toLowerCase();
  const step = String(form.get('step') || 'send').trim().toLowerCase();

  if (!noticeId || !regNoRaw) {
    return c.json({ error: 'Notice and student are required.' }, 400);
  }
  if (!canCounselorAccessNotice(noticeId, authUser.email)) {
    return c.json({ error: 'Access denied for this notice.' }, 403);
  }

  const notice = getNotice(noticeId);
  if (!notice) return c.json({ error: 'Notice not found.' }, 404);
  if (action !== 'send') {
    return c.json({ success: true, status: 'pending' });
  }

  const students = getStudentsForCounselor(authUser.email);
  const normalizedReg = normalizeRegNo(regNoRaw);
  const student = students.find((item) => normalizeRegNo(item.reg_no) === normalizedReg) || null;
  if (!student) {
    return c.json({ error: 'Student not found under your account.' }, 404);
  }

  if (step === 'confirm') {
    const deliveryToken = String(form.get('delivery_token') || '').trim();
    const deliveryOutcome = String(form.get('delivery_outcome') || 'sent').trim().toLowerCase();
    const receipt = getSendReceipt(deliveryToken);

    if (!receipt) {
      if (deliveryOutcome === 'sent' && getNoticeSentRegNos(authUser.email, noticeId).has(normalizedReg)) {
        return c.json({ success: true, status: 'generated', reg_no: normalizedReg });
      }
      return c.json({ error: 'Delivery session expired. Please start again.' }, 400);
    }
    if (String(receipt.kind || '').trim() !== 'notice') {
      return c.json({ error: 'Delivery token does not belong to a notice send.' }, 400);
    }
    if (String(receipt.email || '').trim().toLowerCase() !== authUser.email.toLowerCase()) {
      return c.json({ error: 'Delivery token does not belong to this user.' }, 403);
    }
    if (Number(receipt.notice_id || 0) !== noticeId) {
      return c.json({ error: 'Delivery token does not match this notice.' }, 400);
    }
    if (normalizeRegNo(receipt.reg_no) !== normalizedReg) {
      return c.json({ error: 'Delivery token does not match this student.' }, 400);
    }

    if (deliveryOutcome === 'sent') {
      logNoticeDelivery(
        authUser.email,
        noticeId,
        normalizedReg,
        student.student_name || '',
        String(receipt.message || '').trim() || 'Notice content unavailable',
        {
          whatsapp_link: String(receipt.wa_link || ''),
          status: 'sent',
          delivery_status: 'confirmed',
          send_mode: String(receipt.send_mode || 'app').trim() || 'app',
        },
      );
      deleteSendReceipt(deliveryToken);
      return c.json({ success: true, status: 'generated', reg_no: normalizedReg });
    }

    deleteSendReceipt(deliveryToken);
    return c.json({ success: true, status: deliveryOutcome === 'failed' ? 'failed' : 'skipped', reg_no: normalizedReg });
  }

  const attachments = getNoticeAttachments(noticeId);
  const attachmentLinksText = buildNoticeAttachmentLinksText(c, attachments);
  const noticeTitle = String(form.get('notice_title') || notice.title || '').trim();
  const noticeText = String(form.get('notice_text') || notice.message_text || '').trim();
  const defaultTemplate = buildDefaultNoticeMessage(noticeTitle, noticeText, attachmentLinksText);
  const template = String(form.get('message_template') || '').trim() || defaultTemplate;
  const userRow = getUserByEmail(authUser.email) || null;
  const message = appendNoticeAttachmentBlock(
    fillTemplate(template, {
      app_name: 'RMKCET SHINE',
      reg_no: normalizedReg,
      student_name: student.student_name || normalizedReg,
      department: student.department || String(userRow?.department || ''),
      counselor_name: String(userRow?.name || 'Counselor'),
      notice_title: noticeTitle,
      notice_text: noticeText,
      attachment_links: attachmentLinksText,
    }).trim(),
    attachmentLinksText,
  );

  let phone = normalizePhone(student.parent_phone);
  if (!phone) phone = normalizePhone(student.parent_email);
  if (!phone) {
    for (const candidate of students) {
      if (normalizeRegNo(candidate.reg_no) !== normalizedReg) continue;
      phone = normalizePhone(candidate.parent_phone) || normalizePhone(candidate.parent_email);
      if (phone) break;
    }
  }
  if (!phone) {
    return c.json({ error: `Parent phone number missing for ${normalizedReg}.` }, 400);
  }

  const waLink = getWhatsappLink(phone, message);
  const requestSendMode = String(form.get('send_mode') || 'app').trim().toLowerCase() === 'web' ? 'web' : 'app';

  if (step === 'prepare') {
    const deliveryToken = createSendReceipt({
      kind: 'notice',
      email: authUser.email,
      notice_id: noticeId,
      reg_no: normalizedReg,
      student_name: student.student_name || '',
      message,
      wa_link: waLink,
      send_mode: requestSendMode,
    });
    return c.json({
      success: true,
      status: 'prepared',
      reg_no: normalizedReg,
      wa_link: waLink,
      delivery_token: deliveryToken,
    });
  }

  logNoticeDelivery(authUser.email, noticeId, normalizedReg, student.student_name || '', message, {
    whatsapp_link: waLink,
    send_mode: requestSendMode,
  });
  return c.json({ success: true, status: 'generated', wa_link: waLink });
});

app.get('/notice-files/:token', async (c) => {
  const attachment = getNoticeAttachmentByToken(String(c.req.param('token') || '').trim());
  if (!attachment) return c.text('Not found', 404);
  const bytes = await readFile(resolve(NOTICE_UPLOAD_ROOT, attachment.relative_path)).catch(() => null);
  if (!bytes) return c.text('Not found', 404);
  c.header('Content-Type', attachment.mime_type || 'application/octet-stream');
  c.header('Content-Disposition', `inline; filename=\"${attachment.original_name || 'attachment'}\"`);
  return c.body(bytes);
});

app.get('/api/activity/overview', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const selectedDepartment = String(c.req.query('department') || '').trim().toUpperCase();
  const selectedYear = Number(c.req.query('year') || 0) || null;
  const selectedSemester = String(c.req.query('semester') || '').trim();
  const selectedTestName = String(c.req.query('test_name') || '').trim().toUpperCase();
  const searchQuery = String(c.req.query('q') || '').trim();
  const sortMode = String(c.req.query('sort') || 'pending_first').trim();

  const departments = getVisibleDepartmentsForActor(authUser);
  const yearsByDepartment = getScopedYearsByDepartment(authUser);
  const departmentCode = selectedDepartment && departments.some((item) => item.code.toUpperCase() === selectedDepartment)
    ? selectedDepartment
    : (departments.length === 1 ? departments[0].code.toUpperCase() : '');
  const availableYears = departmentCode
    ? Array.from(new Set(yearsByDepartment.get(departmentCode) || [])).sort((a, b) => a - b)
    : [];
  const yearLevel = selectedYear && availableYears.includes(selectedYear)
    ? selectedYear
    : (availableYears.length === 1 ? availableYears[0] : null);
  const allowedScopes = getAllowedScopesForUser(authUser);
  const tests = departmentCode && yearLevel
    ? getAllUniqueTests({ filterDept: departmentCode, filterYearLevel: yearLevel, allowedScopes })
    : [];

  const activityTestStatus: Record<string, Record<string, boolean>> = {
    '1': { 'IAT 1': false, 'IAT 2': false, 'MODEL EXAM': false },
    '2': { 'IAT 1': false, 'IAT 2': false, 'MODEL EXAM': false },
  };
  for (const test of tests) {
    const sem = String(test.semester || '').trim();
    const testName = String(test.test_name || '').trim().toUpperCase();
    if (activityTestStatus[sem] && Object.prototype.hasOwnProperty.call(activityTestStatus[sem], testName)) {
      activityTestStatus[sem][testName] = true;
    }
  }

  const selectionReady = !!(departmentCode && yearLevel && ['1', '2'].includes(selectedSemester) && selectedTestName);
  const result = selectionReady
    ? getCounselorActivityForTest(departmentCode, yearLevel!, selectedSemester, selectedTestName, searchQuery, sortMode)
    : null;

  return c.json({
    departments,
    selectedDepartment: departmentCode,
    availableYears,
    selectedYear: yearLevel,
    selectedSemester,
    selectedTestName,
    searchQuery,
    sortMode,
    showDepartmentPicker: !departmentCode,
    showYearPicker: !!departmentCode && !yearLevel,
    showSemesterPicker: !!departmentCode && !!yearLevel && !selectionReady,
    testStatus: activityTestStatus,
    result,
  });
});

app.get('/api/activity/scope-report', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const selectedDepartment = String(c.req.query('department') || '').trim().toUpperCase();
  const selectedYear = Number(c.req.query('year') || 0) || null;
  const selectedSemester = String(c.req.query('semester') || '').trim();
  const selectedTestName = String(c.req.query('test_name') || '').trim().toUpperCase();

  return c.json({
    sections: getActivityScopeReport(authUser, {
      department: selectedDepartment,
      year: selectedYear,
      semester: selectedSemester,
      test_name: selectedTestName,
    }),
  });
});

app.get('/api/activity/scope-report/pdf', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const selectedDepartment = String(c.req.query('department') || '').trim().toUpperCase();
  const selectedYear = Number(c.req.query('year') || 0) || null;
  const selectedSemester = String(c.req.query('semester') || '').trim();
  const selectedTestName = String(c.req.query('test_name') || '').trim().toUpperCase();
  const sections = getActivityScopeReport(authUser, {
    department: selectedDepartment,
    year: selectedYear,
    semester: selectedSemester,
    test_name: selectedTestName,
  });

  if (!sections.length) {
    return c.json({ error: 'No uploaded counselor activity sections are available for PDF export.' }, 404);
  }

  try {
    const pdfBuffer = await renderActivityScopePdfWithPython({
      generated_at: new Date().toISOString(),
      sections,
    });
    const fileName = selectedTestName
      ? `activity_${selectedDepartment || 'scope'}_Y${selectedYear || 'all'}_${selectedTestName.replace(/\s+/g, '_')}.pdf`
      : `activity_scope_report_${new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19)}.pdf`;
    return new Response(new Uint8Array(pdfBuffer), {
      headers: {
        'Content-Type': 'application/pdf',
        'Content-Disposition': `attachment; filename="${fileName}"`,
        'Content-Length': String(pdfBuffer.byteLength),
        'Cache-Control': 'no-store',
      },
    });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to render activity scope PDF.' }, 500);
  }
});

app.get('/api/messages/overview', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!canAccessAdminMessages(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const selectedDay = String(c.req.query('day') || '').trim();
  const query = String(c.req.query('q') || '').trim();
  const year = String(c.req.query('year') || '').trim();
  const month = String(c.req.query('month') || '').trim();
  const dayNum = String(c.req.query('day_num') || '').trim();
  const requestedLimit = Number(c.req.query('limit') || 300);
  const messageLimit = Math.min(Math.max(Number.isFinite(requestedLimit) ? requestedLimit : 300, 100), 5000);
  const allowedCounselors = getAllowedCounselorEmailsForActor(authUser);
  const rawMessages = getMessageHistoryFiltered({
    day: selectedDay || null,
    counselorQuery: query || null,
    limit: messageLimit + 1,
    filterYear: year || null,
    filterMonth: month || null,
    filterDay: dayNum || null,
    allowedCounselors,
  });
  const hasMore = rawMessages.length > messageLimit;
  const messages = hasMore ? rawMessages.slice(0, messageLimit) : rawMessages;
  const messageDays = getMessageDays(query || null, allowedCounselors);
  const groupedMap = new Map<string, typeof messages>();
  for (const message of messages) {
    const key = String(message.sent_at || '').slice(0, 10) || 'Unknown';
    if (!groupedMap.has(key)) groupedMap.set(key, []);
    groupedMap.get(key)!.push(message);
  }
  const groups = Array.from(groupedMap.entries()).map(([day, items]) => ({ day, total: items.length, messages: items }));
  const suggestions = getMessageCounselorSuggestions(query, allowedCounselors);
  const uniqueCounselors = new Set(messages.map((item) => item.counselor_email).filter(Boolean)).size;

  return c.json({
    filters: { day: selectedDay, q: query, year, month, day_num: dayNum },
    stats: authUser.role === 'admin' ? getAdminMessageStats() : { total: messages.length, today: 0, active_counselors: uniqueCounselors },
    messages,
    loadedCount: messages.length,
    hasMore,
    groups,
    messageDays,
    suggestions,
  });
});

app.post('/api/messages/delete', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!canAccessAdminMessages(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ id?: number }>().catch(() => ({}))) as { id?: number };
  const deleted = deleteMessageById(Number(body.id || 0));
  return c.json({ success: deleted > 0, deleted });
});

app.post('/api/messages/delete-bulk', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!canAccessAdminMessages(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ ids?: number[] }>().catch(() => ({}))) as { ids?: number[] };
  const deleted = deleteMessagesByIds(Array.isArray(body.ids) ? body.ids : []);
  return c.json({ success: deleted > 0, deleted });
});

app.get('/api/monitoring/overview', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  return c.json({
    sessions: getActiveSessions(),
    stats: getSessionStatistics(),
    history: getSessionHistory(100),
    sessionLog: { ok: true, message: 'Session monitoring active.' },
  });
});

app.post('/api/monitoring/logout-all', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  logoutAllUsers();
  return c.json({ success: true });
});

app.post('/api/monitoring/force-logout/:email', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const email = String(c.req.param('email') || '').trim().toLowerCase();
  if (!email) return c.json({ error: 'Email is required.' }, 400);
  forceLogoutUser(email, 'admin_action');
  return c.json({ success: true });
});

app.post('/api/monitoring/cleanup', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  clearInactiveSessions();
  return c.json({ success: true });
});

app.get('/api/database/overview', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(isSystemAdmin(authUser.role) || isPrincipal(authUser.role))) return c.json({ error: 'Forbidden' }, 403);
  const backups = await listBackupFiles();
  const archiveFiles = await listArchiveFiles();
  const appConfig = getAppConfig();
  return c.json({
    ...backups,
    archiveFiles,
    currentBatchYear: String(appConfig.current_batch_year || ''),
    backupStorageMode: String(appConfig.backup_storage_mode || 'local').trim().toLowerCase() === 'gdrive' ? 'gdrive' : 'local',
  });
});

app.post('/api/database/backup', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(isSystemAdmin(authUser.role) || isPrincipal(authUser.role))) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ batch_name?: string; overwrite?: boolean }>().catch(() => ({}))) as { batch_name?: string; overwrite?: boolean };
  try {
    const batchName = String(body.batch_name || '').trim() || getBatchNameForYearLevel(1);
    const backupPath = await performDatabaseBackup(batchName, !!body.overwrite);
    return c.json({ success: true, message: `Backup created at ${backupPath}` });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Backup failed.' }, 400);
  }
});

app.post('/api/database/delete-backup', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(isSystemAdmin(authUser.role) || isPrincipal(authUser.role))) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ backup_name?: string; password?: string }>().catch(() => ({}))) as { backup_name?: string; password?: string };
  const user = getUserByEmail(authUser.email);
  if (!user || !verifyPassword(String(body.password || ''), String(user.password_hash || ''))) {
    return c.json({ error: 'Password verification failed.' }, 403);
  }
  const backupName = String(body.backup_name || '').trim();
  if (!backupName) return c.json({ error: 'Backup name is required.' }, 400);
  try {
    if (getBackupStorageMode() === 'gdrive') {
      await deleteDriveFileFromPath(['backups'], backupName);
      await clearDrivePath(['backups', `${backupName}${BACKUP_SNAPSHOT_SUFFIX}`]).catch(() => undefined);
      await deleteDriveFileFromPath(['backups'], `${backupName}${BACKUP_SNAPSHOT_SUFFIX}`).catch(() => undefined);
      return c.json({ success: true });
    }
    const backupPath = resolve(BACKUP_DIR, backupName);
    const snapshotDir = getBackupSnapshotDir(backupPath);
    await stat(backupPath);
    await unlink(backupPath);
    await rm(snapshotDir, { recursive: true, force: true });
    return c.json({ success: true });
  } catch {
    return c.json({ error: 'Backup file not found.' }, 404);
  }
});

app.post('/api/database/restore', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(isSystemAdmin(authUser.role) || isPrincipal(authUser.role))) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ backup_name?: string; password?: string }>().catch(() => ({}))) as { backup_name?: string; password?: string };
  const user = getUserByEmail(authUser.email);
  if (!user || !verifyPassword(String(body.password || ''), String(user.password_hash || ''))) {
    return c.json({ error: 'Password verification failed.' }, 403);
  }
  const backupName = String(body.backup_name || '').trim();
  if (!backupName) return c.json({ error: 'Backup name is required.' }, 400);
  let reconnected = false;
  try {
    const preservedSessions = capturePrivilegedSessions();
    checkpointAndCloseDatabase();
    await unlink(`${SHINE_DB_PATH}-wal`).catch(() => undefined);
    await unlink(`${SHINE_DB_PATH}-shm`).catch(() => undefined);
    if (getBackupStorageMode() === 'gdrive') {
      const buffer = await downloadDriveFileFromPath(['backups'], backupName);
      await writeFile(SHINE_DB_PATH, buffer);
      try {
        await writeFile(APP_ENV_FILE, await downloadDriveFileFromPath(['backups', `${backupName}${BACKUP_SNAPSHOT_SUFFIX}`], '.env'));
      } catch {
        // Older backups may not include rebuild settings.
      }
      if (await findDrivePath(['backups', `${backupName}${BACKUP_SNAPSHOT_SUFFIX}`, 'notice_assets'])) {
        await syncDriveDirectoryToLocal(
          ['backups', `${backupName}${BACKUP_SNAPSHOT_SUFFIX}`, 'notice_assets'],
          NOTICE_UPLOAD_ROOT,
          { clearFirst: true },
        );
      }
    } else {
      const backupPath = resolve(BACKUP_DIR, backupName);
      const snapshotDir = getBackupSnapshotDir(backupPath);
      await stat(backupPath);
      await copyFile(backupPath, SHINE_DB_PATH);
      try {
        await stat(resolve(snapshotDir, '.env'));
        await copyFile(resolve(snapshotDir, '.env'), APP_ENV_FILE);
      } catch {
        // Older backups may not include rebuild settings.
      }
      try {
        await stat(resolve(snapshotDir, 'notice_assets'));
        await rm(NOTICE_UPLOAD_ROOT, { recursive: true, force: true });
        await cp(resolve(snapshotDir, 'notice_assets'), NOTICE_UPLOAD_ROOT, { recursive: true, force: true });
      } catch {
        // Older backups may not include notice assets.
      }
    }
    reconnectDatabase();
    restorePrivilegedSessions(preservedSessions);
    if (getBackupStorageMode() === 'gdrive') {
      await syncRuntimeDataMirrorToDrive();
    }
    reconnected = true;
    return c.json({ success: true, reload: true });
  } catch (error) {
    if (!reconnected) {
      try {
        reconnectDatabase();
      } catch {
        // Best effort reconnect after failed restore.
      }
    }
    return c.json({ error: error instanceof Error ? error.message : 'Restore failed.' }, 400);
  }
});

app.post('/api/database/archive-year', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(isSystemAdmin(authUser.role) || isPrincipal(authUser.role))) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ archive_label?: string; password?: string; overwrite?: boolean }>().catch(() => ({}))) as {
    archive_label?: string;
    password?: string;
    overwrite?: boolean;
  };
  const user = getUserByEmail(authUser.email);
  if (!user || !verifyPassword(String(body.password || ''), String(user.password_hash || ''))) {
    return c.json({ error: 'Password verification failed.' }, 403);
  }
  const archiveLabel = String(body.archive_label || '').trim();
  if (!archiveLabel) return c.json({ error: 'Academic year range is required.' }, 400);
  if (!(await latestBackupIsRecentEnough())) {
    return c.json({ error: 'Archive blocked: create a latest backup before archiving the current year.' }, 400);
  }
  try {
    await performYearArchive(archiveLabel, !!body.overwrite);
    await clearExamDatabaseOnly();
    await rm(NOTICE_UPLOAD_ROOT, { recursive: true, force: true }).catch(() => undefined);
    await mkdir(NOTICE_UPLOAD_ROOT, { recursive: true });
    if (getBackupStorageMode() === 'gdrive') {
      await syncRuntimeDataMirrorToDrive();
    }
    return c.json({ success: true, reload: true });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Archive failed.' }, 400);
  }
});

app.post('/api/database/clear', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(isSystemAdmin(authUser.role) || isPrincipal(authUser.role))) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ password?: string }>().catch(() => ({}))) as { password?: string };
  const user = getUserByEmail(authUser.email);
  if (!user || !verifyPassword(String(body.password || ''), String(user.password_hash || ''))) {
    return c.json({ error: 'Password verification failed.' }, 403);
  }
  if (!(await latestBackupIsRecentEnough())) {
    return c.json({ error: 'Clear blocked: create a latest backup before clearing exam data.' }, 400);
  }
  try {
    logoutAllUsers();
    await clearExamDatabaseOnly();
    if (getBackupStorageMode() === 'gdrive') {
      await syncRuntimeDataMirrorToDrive();
    }
    deleteCookie(c, SESSION_COOKIE, { path: '/' });
    return c.json({ success: true, relogin: true });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Clear failed.' }, 400);
  }
});

app.get('/api/config/overview', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  let envContent = '';
  try {
    envContent = await readFile(APP_ENV_FILE, 'utf-8');
  } catch {
    envContent = '';
  }
  return c.json({
    appConfig: sanitizeAppConfigForClient(getAppConfig(), authUser),
    envContent,
    smtpStatus: getSmtpStatus(),
    resetUsers: listUsersForActor(authUser),
  });
});

app.post('/api/config/update', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<Record<string, unknown>>().catch(() => ({}))) as Record<string, unknown>;
  const currentConfig = getAppConfig();
  const currentStorageMode = getBackupStorageMode(currentConfig);

  const timeoutHours = Number(body.session_timeout_hours || 24);
  if (!Number.isFinite(timeoutHours) || timeoutHours < 1 || timeoutHours > 168) {
    return c.json({ error: 'Session timeout must be between 1 and 168 hours.' }, 400);
  }
  const heartbeat = Number(body.session_heartbeat_interval || 30);
  if (!Number.isFinite(heartbeat) || heartbeat < 10 || heartbeat > 120) {
    return c.json({ error: 'Heartbeat interval must be between 10 and 120 seconds.' }, 400);
  }

  const settings: Record<string, string> = {
    session_timeout: String(Math.round(timeoutHours) * 3600),
    session_heartbeat_interval: String(Math.round(heartbeat)),
    allow_concurrent_sessions: body.allow_concurrent_sessions ? 'true' : 'false',
    max_concurrent_sessions: body.allow_concurrent_sessions ? String(Math.max(1, Math.min(5, Number(body.max_concurrent_sessions || 1) || 1))) : '1',
    enable_periodic_backups: body.enable_periodic_backups ? 'true' : 'false',
    periodic_backup_hour: String(Math.max(0, Math.min(23, Number(body.periodic_backup_hour || 0) || 0))),
    periodic_backup_minute: String(Math.max(0, Math.min(59, Number(body.periodic_backup_minute || 0) || 0))),
    tutorial_master_enabled: body.tutorial_master_enabled ? 'true' : 'false',
    tutorial_counselor_enabled: body.tutorial_master_enabled && body.tutorial_counselor_enabled ? 'true' : 'false',
    tutorial_hod_enabled: body.tutorial_master_enabled && body.tutorial_hod_enabled ? 'true' : 'false',
    tutorial_deo_enabled: body.tutorial_master_enabled && body.tutorial_deo_enabled ? 'true' : 'false',
    tutorial_principal_enabled: body.tutorial_master_enabled && body.tutorial_principal_enabled ? 'true' : 'false',
    disable_default_admin_on_new_system_admin: body.disable_default_admin_on_new_system_admin ? 'true' : 'false',
    require_otp_on_password_reset: body.require_otp_on_password_reset ? 'true' : 'false',
    require_otp_on_login: body.require_otp_on_login ? 'true' : 'false',
    counselor_login_otp_enabled: body.require_otp_on_login && body.counselor_login_otp_enabled ? 'true' : 'false',
    notice_copy_as_image: body.notice_copy_as_image ? 'true' : 'false',
    activity_copy_as_image: body.activity_copy_as_image ? 'true' : 'false',
    backup_storage_mode: String(body.backup_storage_mode || currentConfig.backup_storage_mode || 'local').trim().toLowerCase() === 'gdrive' ? 'gdrive' : 'local',
    enable_counselor_batch_send: body.enable_counselor_batch_send ? 'true' : 'false',
    counselor_batch_send_delay_seconds: String(Math.max(1, Math.min(30, Number(body.counselor_batch_send_delay_seconds || currentConfig.counselor_batch_send_delay_seconds || 4) || 4))),
    current_batch_year: String(body.current_batch_year || currentConfig.current_batch_year || '').trim() || currentConfig.current_batch_year,
    google_oauth_enabled: body.google_oauth_enabled ? 'true' : 'false',
    google_oauth_client_id: String(body.google_oauth_client_id || currentConfig.google_oauth_client_id || '').trim(),
    google_oauth_client_secret: String(body.google_oauth_client_secret || currentConfig.google_oauth_client_secret || '').trim(),
    google_oauth_allowed_domain: String(body.google_oauth_allowed_domain || '').trim().toLowerCase().replace(/^@/, ''),
    google_oauth_redirect_base_url: String(body.google_oauth_redirect_base_url || '')
      .trim()
      .replace(/\/+$/, '')
      .replace(/\/auth\/google\/callback$/i, ''),
    google_oauth_bulk_password_mode: String(body.google_oauth_bulk_password_mode || currentConfig.google_oauth_bulk_password_mode || 'sheet').trim().toLowerCase() === 'override' ? 'override' : 'sheet',
    google_oauth_bulk_override_password: String(body.google_oauth_bulk_override_password || currentConfig.google_oauth_bulk_override_password || '').trim(),
    google_drive_refresh_token: String(body.google_drive_refresh_token || currentConfig.google_drive_refresh_token || '').trim(),
    google_drive_folder_id: String(body.google_drive_folder_id || currentConfig.google_drive_folder_id || '').trim(),
    smtp_server: String(body.smtp_server || currentConfig.smtp_server || '').trim(),
    smtp_port: String(body.smtp_port || currentConfig.smtp_port || '587').trim(),
    smtp_username: String(body.smtp_username || currentConfig.smtp_username || '').trim(),
    smtp_password: String(body.smtp_password || currentConfig.smtp_password || '').trim(),
    email_from: String(body.email_from || currentConfig.email_from || '').trim(),
    color_primary: String(body.color_primary || currentConfig.color_primary || '').trim(),
    color_primary_dark: String(body.color_primary_dark || currentConfig.color_primary_dark || '').trim(),
    color_secondary: String(body.color_secondary || currentConfig.color_secondary || '').trim(),
    color_accent: String(body.color_accent || currentConfig.color_accent || '').trim(),
    color_success: String(body.color_success || currentConfig.color_success || '').trim(),
    color_warning: String(body.color_warning || currentConfig.color_warning || '').trim(),
    color_danger: String(body.color_danger || currentConfig.color_danger || '').trim(),
    color_info: String(body.color_info || currentConfig.color_info || '').trim(),
    color_bg_primary: String(body.color_bg_primary || currentConfig.color_bg_primary || '').trim(),
    color_bg_secondary: String(body.color_bg_secondary || currentConfig.color_bg_secondary || '').trim(),
    color_bg_card: String(body.color_bg_card || currentConfig.color_bg_card || '').trim(),
    color_text: String(body.color_text || currentConfig.color_text || '').trim(),
    color_text_dim: String(body.color_text_dim || currentConfig.color_text_dim || '').trim(),
    color_text_muted: String(body.color_text_muted || currentConfig.color_text_muted || '').trim(),
    color_border: String(body.color_border || currentConfig.color_border || '').trim(),
  };

  const nextDriveSettings = getGoogleDriveSettings({
    ...currentConfig,
    ...settings,
  });
  if (settings.backup_storage_mode === 'gdrive' && !nextDriveSettings.enabled) {
    return c.json({ error: 'Google Drive mode requires Google OAuth client ID, client secret, and a Drive refresh token.' }, 400);
  }

  updateAppConfigBulk(settings);
  if (currentStorageMode !== settings.backup_storage_mode) {
    try {
      await migrateStorageArtifacts(currentStorageMode, settings.backup_storage_mode as 'local' | 'gdrive', nextDriveSettings);
    } catch (error) {
      updateAppConfig('backup_storage_mode', currentStorageMode);
      return c.json({ error: error instanceof Error ? error.message : 'Failed to migrate backup storage artifacts.' }, 400);
    }
  }
  await upsertEnvValues(APP_ENV_FILE, {
    SMTP_SERVER: settings.smtp_server,
    SMTP_PORT: settings.smtp_port,
    SMTP_USERNAME: settings.smtp_username,
    SMTP_PASSWORD: settings.smtp_password,
    EMAIL_FROM: settings.email_from,
  });
  return c.json({ success: true, appConfig: sanitizeAppConfigForClient(getAppConfig(), authUser), smtpStatus: getSmtpStatus() });
});

app.post('/api/config/env-update', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ env_content?: string }>().catch(() => ({}))) as { env_content?: string };
  const content = String(body.env_content || '');
  if (!content.trim()) return c.json({ error: 'Environment content cannot be empty.' }, 400);
  await writeFile(APP_ENV_FILE, content, 'utf-8');
  return c.json({ success: true });
});

app.get('/api/config/smtp-status', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  return c.json({ success: true, status: getSmtpStatus() });
});

app.post('/api/config/smtp-test', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const status = getSmtpStatus();
  if (status.state !== 'ready') {
    return c.json({ success: false, message: 'SMTP is not ready. Update credentials first.' }, 400);
  }
  return c.json({ success: true, message: 'SMTP configuration looks ready. Live email test is not required for rebuild validation.' });
});

app.post('/api/users/reset-password', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ target_email?: string; new_password?: string; confirm_password?: string; force_logout?: boolean }>().catch(() => ({}))) as {
    target_email?: string;
    new_password?: string;
    confirm_password?: string;
    force_logout?: boolean;
  };
  const targetEmail = String(body.target_email || '').trim().toLowerCase();
  const newPassword = String(body.new_password || '');
  const confirmPassword = String(body.confirm_password || '');
  if (!targetEmail || !newPassword || !confirmPassword) return c.json({ error: 'User and both password fields are required.' }, 400);
  if (newPassword !== confirmPassword) return c.json({ error: 'New password and confirm password do not match.' }, 400);
  if (newPassword.length < 6) return c.json({ error: 'Password must be at least 6 characters.' }, 400);
  const user = getUserByEmail(targetEmail);
  if (!user) return c.json({ error: 'Selected user was not found.' }, 404);
  updateUserPassword(targetEmail, newPassword);
  if (body.force_logout && targetEmail !== authUser.email) {
    forceLogoutUser(targetEmail, 'admin_password_reset');
  }
  return c.json({ success: true });
});

app.get('/api/admin/server-console', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const limit = Number(c.req.query('limit') || SERVER_CONSOLE_DEFAULT_VIEW_LINES) || SERVER_CONSOLE_DEFAULT_VIEW_LINES;
  return c.json({
    lines: getServerConsoleLines(limit),
    meta: `Showing latest ${Math.max(1, Math.min(200, limit))} lines`,
  });
});

app.get('/api/panel-status', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  return c.json({
    role: authUser.role,
    isAdminPortalRole: isAdminPortalRole(authUser.role),
    allowedTabs: allowedTabsForRole(authUser.role),
    defaultTab: defaultTabForRole(authUser.role),
  });
});

app.get('/auth/google/start', (c) => {
  const appConfig = getAppConfig();
  const oauth = getGoogleOauthSettings(appConfig);
  if (!oauth.enabled) {
    const target = new URL(buildGoogleOauthClientRedirect());
    target.searchParams.set('error', 'google_disabled');
    return c.redirect(target.toString());
  }

  const state = randomUUID().replace(/-/g, '');
  setCookie(c, GOOGLE_STATE_COOKIE, state, {
    path: '/',
    httpOnly: true,
    sameSite: 'Lax',
    maxAge: 600,
  });

  const params = new URLSearchParams({
    client_id: oauth.clientId,
    redirect_uri: buildGoogleOauthRedirectUri(appConfig),
    response_type: 'code',
    scope: 'openid email profile',
    state,
    prompt: 'select_account',
  });
  if (oauth.allowedDomain) {
    params.set('hd', oauth.allowedDomain);
  }

  return c.redirect(`https://accounts.google.com/o/oauth2/v2/auth?${params.toString()}`);
});

app.get('/auth/google/callback', async (c) => {
  const appConfig = getAppConfig();
  const oauth = getGoogleOauthSettings(appConfig);
  const target = new URL(buildGoogleOauthClientRedirect());

  if (!oauth.enabled) {
    target.searchParams.set('error', 'google_disabled');
    return c.redirect(target.toString());
  }

  const oauthError = String(c.req.query('error') || '').trim();
  if (oauthError) {
    target.searchParams.set('error', oauthError);
    target.searchParams.set(
      'error_description',
      String(c.req.query('error_description') || 'Google sign-in was cancelled.'),
    );
    deleteCookie(c, GOOGLE_STATE_COOKIE, { path: '/' });
    return c.redirect(target.toString());
  }

  const state = String(c.req.query('state') || '').trim();
  const expectedState = String(getCookie(c, GOOGLE_STATE_COOKIE) || '').trim();
  deleteCookie(c, GOOGLE_STATE_COOKIE, { path: '/' });
  if (!state || !expectedState || state !== expectedState) {
    target.searchParams.set('error', 'state_mismatch');
    return c.redirect(target.toString());
  }

  const code = String(c.req.query('code') || '').trim();
  if (!code) {
    target.searchParams.set('error', 'missing_code');
    return c.redirect(target.toString());
  }

  try {
    const tokenResponse = await fetch('https://oauth2.googleapis.com/token', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/x-www-form-urlencoded',
        Accept: 'application/json',
      },
      body: new URLSearchParams({
        code,
        client_id: oauth.clientId,
        client_secret: oauth.clientSecret,
        redirect_uri: buildGoogleOauthRedirectUri(appConfig),
        grant_type: 'authorization_code',
      }),
    });
    const tokenPayload = (await tokenResponse.json()) as Record<string, unknown>;
    const accessToken = String(tokenPayload.access_token || '').trim();
    if (!tokenResponse.ok || !accessToken) {
      target.searchParams.set('error', 'token_exchange_failed');
      return c.redirect(target.toString());
    }

    const profileResponse = await fetch('https://openidconnect.googleapis.com/v1/userinfo', {
      headers: {
        Authorization: `Bearer ${accessToken}`,
        Accept: 'application/json',
      },
    });
    const profile = (await profileResponse.json()) as Record<string, unknown>;
    const email = String(profile.email || '').trim().toLowerCase();
    const emailVerified = Boolean(profile.email_verified ?? true);

    if (!profileResponse.ok || !email || !emailVerified) {
      target.searchParams.set('error', 'invalid_google_profile');
      return c.redirect(target.toString());
    }

    if (oauth.allowedDomain) {
      const emailDomain = email.includes('@') ? email.split('@')[1]!.toLowerCase() : '';
      if (emailDomain !== oauth.allowedDomain) {
        target.searchParams.set('error', 'invalid_domain');
        target.searchParams.set('allowed_domain', oauth.allowedDomain);
        return c.redirect(target.toString());
      }
    }

    const userRow = getUserByEmail(email);
    if (!userRow) {
      target.searchParams.set('error', 'user_not_linked');
      target.searchParams.set('error_description', 'Account not registered.');
      return c.redirect(target.toString());
    }

    const access = checkUserAccess(email);
    if (!access.allowed) {
      target.searchParams.set('error', 'access_denied');
      target.searchParams.set('error_description', access.message);
      return c.redirect(target.toString());
    }

    const allowConcurrent = String(appConfig.allow_concurrent_sessions || 'false').toLowerCase() === 'true';
    clearChallengeCookie(c, LOGIN_OTP_COOKIE);
    clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
    clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
    finalizeLogin(c, userRow, !allowConcurrent, 'google');
    target.searchParams.set('success', '1');
    return c.redirect(target.toString());
  } catch {
    target.searchParams.set('error', 'oauth_callback_failed');
    return c.redirect(target.toString());
  }
});

app.get('*', async (c) => {
  const pathname = decodeURIComponent(new URL(c.req.url).pathname || '/');
  if (pathname.startsWith('/api/') || pathname.startsWith('/auth/')) {
    return c.text('Not found.', 404);
  }
  const relativePath = pathname === '/' ? 'index.html' : pathname.replace(/^\/+/, '');
  const requestedFile = resolve(CLIENT_DIST_ROOT, relativePath);
  const isInsideDistRoot =
    requestedFile === CLIENT_DIST_ROOT ||
    requestedFile.startsWith(`${CLIENT_DIST_ROOT}/`) ||
    requestedFile.startsWith(`${CLIENT_DIST_ROOT}\\`);

  if (isInsideDistRoot) {
    try {
      const fileStat = await stat(requestedFile);
      if (fileStat.isFile()) {
        const fileData = await readFile(requestedFile);
        c.header('Content-Type', getStaticMimeType(requestedFile));
        return new Response(new Uint8Array(fileData));
      }
    } catch {
      // Fall back to SPA shell for client-side routes.
    }
  }

  try {
    const indexPath = resolve(CLIENT_DIST_ROOT, 'index.html');
    const indexData = await readFile(indexPath);
    c.header('Content-Type', 'text/html; charset=utf-8');
    return new Response(new Uint8Array(indexData));
  } catch {
    return c.text('Client build not found. Run npm run build in the rebuild root.', 404);
  }
});

serve({
  fetch: app.fetch,
  hostname: SERVER_HOST,
  port: SERVER_PORT,
});

appendServerConsoleLine(`Shine rebuild server booted on http://[${SERVER_HOST}]:${SERVER_PORT}`);
console.log(`Shine rebuild server running on http://[${SERVER_HOST}]:${SERVER_PORT}`);

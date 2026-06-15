import { createHash, randomUUID } from 'node:crypto';
import { spawn } from 'node:child_process';
import { copyFile, cp, mkdir, mkdtemp, readFile, readdir, rename, rm, stat, unlink, writeFile } from 'node:fs/promises';
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
  ARCHIVE_VIEW_COOKIE,
  ARCHIVE_DIR,
  BACKUP_DIR,
  CLIENT_ORIGIN,
  CLIENT_ORIGINS,
  DEFAULT_SYSTEM_ADMIN_EMAIL,
  DESKTOP_INSTALLER_ROOT,
  GOOGLE_LOGIN_CONFLICT_COOKIE,
  GOOGLE_STATE_COOKIE,
  LOGIN_OTP_COOKIE,
  LOGIN_ROLE_COOKIE,
  NOTICE_UPLOAD_ROOT,
  PASSWORD_RESET_COOKIE,
  SERVER_ORIGIN,
  SERVER_HOST,
  SERVER_PORT,
  SERVER_ROOT,
  SESSION_COOKIE,
  SESSION_NOTICE_COOKIE,
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
  getCounselorActivityScopeSnapshot,
  getCounselorActivitySummary,
  getCounselorMessageHistory,
  getCounselorMessageStats,
  getCounselorSendNoticeRows,
  getCounselorSendReportRows,
  getDashboardMetrics,
  getDepartments,
  getLoginCandidatesByIdentifier,
  getNotice,
  getNoticeAttachmentByToken,
  getNoticeAttachments,
  getNoticeCompletionRows,
  getNoticeRecordsForActor,
  getNoticeSentRegNos,
  getNotificationStatesForUser,
  getNoticeScopePairs,
  getMessageCounselorSuggestions,
  getMessageDays,
  getMessageHistoryFiltered,
  getOauthAttemptStatistics,
  getLogoutReasonForSession,
  getSessionLastActivityInfo,
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
  getUsersByLoginEmail,
  getUsersForActor,
  getScopesForUser,
  getSubjectById,
  getSubjectScopeSnapshot,
  createSubjectRecord,
  deleteCdpSubjectSnapshot,
  deleteSubjectRecord,
  getCdpSubjectSnapshot,
  listSubjectsForActor,
  listCdpSubjectSnapshots,
  logMessage,
  logNoticeDelivery,
  listUsersForActor,
  lockCounselorsForDepartment,
  lockUserForDuration,
  lockUser,
  logoutAllUsers,
  logoutSession,
  normalizeAllowedTestName,
  recordAuthFailureAttempt,
  recordOauthLoginAttempt,
  reconnectDatabase,
  registerSession,
  saveUploadedTestMarks,
  saveCounselorStudent,
  setChiefAdminScopes,
  toAuthUser,
  toggleDepartment,
  unlockCounselorsForDepartment,
  updateNotificationStatesForUser,
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
  updateSubjectRecord,
  upsertCdpSubjectSnapshot,
  validateSession,
  verifyPassword,
  withDatabaseContext,
  openReadOnlyDatabase,
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
  html[data-shine-theme="dark"] {
    --bg: #08101d;
    --panel: rgba(12, 20, 36, .96);
    --panel-soft: rgba(18, 27, 46, .94);
    --border: rgba(102, 126, 234, .22);
    --border-soft: rgba(148, 163, 184, .18);
    --text: #e5ecfb;
    --text-dim: #b3c0d9;
    --text-muted: #8ea0bf;
    --accent: #7c9dff;
    --accent-2: #9a74d9;
    --shadow: 0 24px 54px rgba(2, 8, 23, .45);
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
    background: linear-gradient(180deg, rgba(255,255,255,.03), rgba(255,255,255,.015));
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
const FOOTER_THEME_BOOT_SCRIPT = `
  try {
    var shineTheme = localStorage.getItem('theme') === 'dark' ? 'dark' : 'light';
    document.documentElement.setAttribute('data-shine-theme', shineTheme);
  } catch {
    document.documentElement.setAttribute('data-shine-theme', 'light');
  }
`;
const TEST_MODE_IDLE_TIMEOUT_MS = 2 * 60 * 1000;

type PendingLoginOtpChallenge = {
  email: string;
  loginEmail: string;
  role: string;
  identifier?: string;
  displayName?: string;
  accountEmails?: string[];
  roleSelectionOptions?: Array<{
    accountEmail: string;
    role: string;
    name: string;
    designation?: string;
    department: string;
    year_level: number;
  }>;
  forceLogoutOthers: boolean;
  otpHash: string;
  expiresAt: number;
  requestedAt: number;
  invalidAttempts: number;
};

type PendingLoginRoleSelectionChallenge = {
  identifier: string;
  loginEmail: string;
  authMethod: 'password' | 'google';
  forceLogoutOthers: boolean;
  displayName: string;
  options: Array<{
    accountEmail: string;
    role: string;
    name: string;
    designation?: string;
    department: string;
    year_level: number;
  }>;
  otpVerified?: boolean;
  expiresAt: number;
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

type PendingGoogleOauthState = {
  expiresAt: number;
};

type PendingGoogleLoginConflictChallenge = {
  email: string;
  expiresAt: number;
};

type ActiveTestModeBlock = {
  adminSessionId: string;
  adminEmail: string;
  targetEmail: string;
  startedAt: number;
};

type SessionEndNotice = {
  title: string;
  message: string;
  reason: string;
};

const pendingLoginOtpChallenges = new Map<string, PendingLoginOtpChallenge>();
const pendingLoginRoleSelectionChallenges = new Map<string, PendingLoginRoleSelectionChallenge>();
const pendingPasswordResetChallenges = new Map<string, PendingPasswordResetChallenge>();
const pendingSelfResetOtpChallenges = new Map<string, PendingSelfResetOtpChallenge>();
const pendingGoogleOauthStates = new Map<string, PendingGoogleOauthState>();
const pendingGoogleLoginConflictChallenges = new Map<string, PendingGoogleLoginConflictChallenge>();
const activeTestModeBlocksByTarget = new Map<string, ActiveTestModeBlock>();
const activeTestModeTargetByAdminSession = new Map<string, string>();
const GOOGLE_OAUTH_STATE_TTL_MS = 10 * 60 * 1000;

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

function parseSqlTimestamp(value: string | null | undefined) {
  const raw = String(value || '').trim();
  if (!raw) return null;
  const normalized = raw.includes('T') ? raw : raw.replace(' ', 'T');
  const assumedUtc = /(?:Z|[+-]\d{2}:\d{2})$/i.test(normalized) ? normalized : `${normalized}Z`;
  const timestamp = Date.parse(assumedUtc);
  return Number.isFinite(timestamp) ? timestamp : null;
}

function isTimestampOlderThan(value: string | null | undefined, ageMs: number) {
  const timestamp = parseSqlTimestamp(value);
  return timestamp !== null && Date.now() - timestamp > ageMs;
}

function getUserLoginEmail(userRow: Record<string, unknown> | null | undefined) {
  return String(userRow?.login_email || userRow?.email || '').trim().toLowerCase();
}

function getOtpLockHours(appConfig: Record<string, string>) {
  const hours = Number(appConfig.otp_login_lock_hours || 5);
  return Number.isFinite(hours) && hours >= 1 && hours <= 168 ? Math.round(hours) : 5;
}

function formatHoursLabel(hours: number) {
  return `${hours} hour${hours === 1 ? '' : 's'}`;
}

function isLoginOtpRequiredForUser(userRow: Record<string, unknown>, appConfig: Record<string, string>) {
  if (!getBooleanConfigValue(appConfig.require_otp_on_login)) return false;
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

function createGoogleOauthState() {
  cleanupExpiredChallengeMap(pendingGoogleOauthStates);
  const state = randomUUID().replace(/-/g, '');
  pendingGoogleOauthStates.set(state, {
    expiresAt: nowMs() + GOOGLE_OAUTH_STATE_TTL_MS,
  });
  return state;
}

function consumeGoogleOauthState(state: string) {
  cleanupExpiredChallengeMap(pendingGoogleOauthStates);
  const normalizedState = String(state || '').trim();
  if (!normalizedState) return false;
  const pendingState = pendingGoogleOauthStates.get(normalizedState);
  pendingGoogleOauthStates.delete(normalizedState);
  return isOtpCookieFresh(pendingState);
}

function createGoogleLoginConflictChallenge(c: Context, email: string) {
  cleanupExpiredChallengeMap(pendingGoogleLoginConflictChallenges);
  const token = randomUUID();
  pendingGoogleLoginConflictChallenges.set(token, {
    email: String(email || '').trim().toLowerCase(),
    expiresAt: nowMs() + GOOGLE_OAUTH_STATE_TTL_MS,
  });
  setChallengeCookie(c, GOOGLE_LOGIN_CONFLICT_COOKIE, token, GOOGLE_OAUTH_STATE_TTL_MS);
}

function buildRoleSelectionOptions(rows: Array<Record<string, unknown>>) {
  return rows.map((userRow) => ({
    accountEmail: String(userRow.email || '').trim().toLowerCase(),
    role: String(userRow.role || '').trim().toLowerCase(),
    name: String(userRow.name || userRow.login_email || userRow.email || '').trim(),
    designation: String(userRow.designation || '').trim(),
    department: String(userRow.department || '').trim().toUpperCase(),
    year_level: Number(userRow.year_level || 1) || 1,
  }));
}

function getAvailableRoleSwitchOptionsForUser(authUser: ReturnType<typeof toAuthUser> | null) {
  const loginEmail = String(authUser?.login_email || authUser?.email || '').trim().toLowerCase();
  if (!loginEmail) return [];
  const currentEmail = String(authUser?.email || '').trim().toLowerCase();
  const accessibleRows = getUsersByLoginEmail(loginEmail)
    .filter((row) => {
      const rowEmail = String(row.email || '').trim().toLowerCase();
      if (!rowEmail) return false;
      return rowEmail === currentEmail || checkUserAccess(rowEmail).allowed;
    })
    .filter((row, index, list) => list.findIndex((entry) => String(entry.email || '').trim().toLowerCase() === String(row.email || '').trim().toLowerCase()) === index);
  const options = buildRoleSelectionOptions(accessibleRows as Array<Record<string, unknown>>);
  return options.sort((left, right) => {
    if (left.accountEmail === currentEmail) return -1;
    if (right.accountEmail === currentEmail) return 1;
    return left.accountEmail.localeCompare(right.accountEmail);
  });
}

function createLoginRoleSelectionChallenge(
  c: Context,
  payload: {
    identifier: string;
    loginEmail: string;
    authMethod: 'password' | 'google';
    forceLogoutOthers: boolean;
    displayName: string;
    options: Array<{
      accountEmail: string;
      role: string;
      name: string;
      designation?: string;
      department: string;
      year_level: number;
    }>;
    otpVerified?: boolean;
  },
) {
  cleanupExpiredChallengeMap(pendingLoginRoleSelectionChallenges);
  const token = randomUUID();
  pendingLoginRoleSelectionChallenges.set(token, {
    ...payload,
    expiresAt: nowMs() + GOOGLE_OAUTH_STATE_TTL_MS,
  });
  setChallengeCookie(c, LOGIN_ROLE_COOKIE, token, GOOGLE_OAUTH_STATE_TTL_MS);
}

function readLoginRoleSelectionChallenge(c: Context) {
  cleanupExpiredChallengeMap(pendingLoginRoleSelectionChallenges);
  const token = String(getCookie(c, LOGIN_ROLE_COOKIE) || '').trim();
  const challenge = token ? pendingLoginRoleSelectionChallenges.get(token) : null;
  if (!challenge || !isOtpCookieFresh(challenge)) {
    if (token) pendingLoginRoleSelectionChallenges.delete(token);
    clearChallengeCookie(c, LOGIN_ROLE_COOKIE);
    return null;
  }
  return { token, challenge };
}

function clearLoginRoleSelectionChallenge(c: Context, token?: string) {
  const normalizedToken = String(token || getCookie(c, LOGIN_ROLE_COOKIE) || '').trim();
  if (normalizedToken) {
    pendingLoginRoleSelectionChallenges.delete(normalizedToken);
  }
  clearChallengeCookie(c, LOGIN_ROLE_COOKIE);
}

function buildSessionEndNotice(reason: string | null | undefined): SessionEndNotice | null {
  const normalizedReason = String(reason || '').trim().toLowerCase();
  if (!normalizedReason || normalizedReason === 'logout') return null;
  if (normalizedReason === 'new_login') {
    return {
      title: 'Logged Out',
      message: 'This account was signed out because a new login was completed on another device.',
      reason: normalizedReason,
    };
  }
  if (normalizedReason === 'test_mode_preview') {
    return {
      title: 'Logged Out For Test Mode',
      message: 'This account was signed out because an admin entered account test mode for review.',
      reason: normalizedReason,
    };
  }
  if (normalizedReason === 'session_timeout') {
    return {
      title: 'Session Expired',
      message: 'Your session expired due to inactivity. Please sign in again.',
      reason: normalizedReason,
    };
  }
  if (normalizedReason === 'admin_password_reset') {
    return {
      title: 'Logged Out',
      message: 'Your account was signed out because an administrator reset your password.',
      reason: normalizedReason,
    };
  }
  if (normalizedReason === 'account_locked') {
    return {
      title: 'Account Locked',
      message: 'Your account was locked and the current session was closed.',
      reason: normalizedReason,
    };
  }
  return {
    title: 'Logged Out',
    message: 'Your session ended and you need to sign in again.',
    reason: normalizedReason,
  };
}

function setSessionEndNoticeCookie(c: Context, notice: SessionEndNotice) {
  setCookie(c, SESSION_NOTICE_COOKIE, JSON.stringify(notice), {
    path: '/',
    httpOnly: false,
    sameSite: 'Lax',
    maxAge: 180,
  });
}

function readSessionEndNotice(c: Context) {
  const raw = String(getCookie(c, SESSION_NOTICE_COOKIE) || '').trim();
  if (!raw) return null;
  try {
    const parsed = JSON.parse(raw) as Partial<SessionEndNotice>;
    return {
      title: String(parsed.title || 'Logged Out').trim() || 'Logged Out',
      message: String(parsed.message || 'Your session ended and you need to sign in again.').trim(),
      reason: String(parsed.reason || '').trim().toLowerCase(),
    } satisfies SessionEndNotice;
  } catch {
    return null;
  }
}

function setArchiveViewCookie(c: Context, archiveName: string) {
  setCookie(c, ARCHIVE_VIEW_COOKIE, String(archiveName || '').trim(), {
    path: '/',
    httpOnly: false,
    sameSite: 'Lax',
    maxAge: 7 * 24 * 60 * 60,
  });
}

function clearArchiveViewCookie(c: Context) {
  deleteCookie(c, ARCHIVE_VIEW_COOKIE, { path: '/' });
}

function buildArchiveViewState(archiveName: string) {
  return {
    active: true,
    archiveName,
    academicYear: getAcademicYearLabelFromArchiveName(archiveName),
  };
}

function releaseTestModeBlockForAdminSession(adminSessionId: string) {
  const normalizedSessionId = String(adminSessionId || '').trim();
  if (!normalizedSessionId) return;
  const targetEmail = activeTestModeTargetByAdminSession.get(normalizedSessionId);
  if (!targetEmail) return;
  activeTestModeTargetByAdminSession.delete(normalizedSessionId);
  const block = activeTestModeBlocksByTarget.get(targetEmail);
  if (block?.adminSessionId === normalizedSessionId) {
    activeTestModeBlocksByTarget.delete(targetEmail);
  }
}

function assignTestModeBlock(adminSessionId: string, adminEmail: string, targetEmail: string) {
  const normalizedAdminSessionId = String(adminSessionId || '').trim();
  const normalizedAdminEmail = String(adminEmail || '').trim().toLowerCase();
  const normalizedTargetEmail = String(targetEmail || '').trim().toLowerCase();
  if (!normalizedAdminSessionId || !normalizedTargetEmail) return;
  releaseTestModeBlockForAdminSession(normalizedAdminSessionId);
  activeTestModeBlocksByTarget.set(normalizedTargetEmail, {
    adminSessionId: normalizedAdminSessionId,
    adminEmail: normalizedAdminEmail,
    targetEmail: normalizedTargetEmail,
    startedAt: nowMs(),
  });
  activeTestModeTargetByAdminSession.set(normalizedAdminSessionId, normalizedTargetEmail);
}

function getTestModeBlockForUser(email: string) {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  const block = activeTestModeBlocksByTarget.get(normalizedEmail) || null;
  if (!block) return null;
  const lastActivity = getSessionLastActivityInfo(block.adminSessionId);
  if (!lastActivity || !Number(lastActivity.is_active) || isTimestampOlderThan(lastActivity.last_activity, TEST_MODE_IDLE_TIMEOUT_MS)) {
    releaseTestModeBlockForAdminSession(block.adminSessionId);
    return null;
  }
  const adminSession = validateSession(block.adminSessionId);
  if (!adminSession || adminSession.role !== 'admin') {
    releaseTestModeBlockForAdminSession(block.adminSessionId);
    return null;
  }
  return block;
}

async function createLoginOtpChallenge(c: Context, userRow: Record<string, unknown>, forceLogoutOthers: boolean) {
  cleanupExpiredChallengeMap(pendingLoginOtpChallenges);
  const email = String(userRow.email || '').trim().toLowerCase();
  const loginEmail = getUserLoginEmail(userRow);
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(loginEmail, 'Login', otpCode);
  if (!sent) return null;
  const token = randomUUID();
  pendingLoginOtpChallenges.set(token, {
    email,
    loginEmail,
    role: String(userRow.role || '').trim().toLowerCase(),
    identifier: loginEmail,
    displayName: String(userRow.name || loginEmail || email).trim(),
    accountEmails: [email],
    forceLogoutOthers,
    otpHash: hashOtp(otpCode),
    expiresAt: nowMs() + OTP_EXPIRY_MS,
    requestedAt: nowMs(),
    invalidAttempts: 0,
  });
  setChallengeCookie(c, LOGIN_OTP_COOKIE, token);
  return { maskedEmail: maskEmailAddress(loginEmail) };
}

async function refreshLoginOtpChallenge(c: Context, token: string, challenge: PendingLoginOtpChallenge) {
  if (nowMs() - Number(challenge.requestedAt || 0) < OTP_RESEND_THROTTLE_MS) {
    throw new Error('Please wait 30 seconds before requesting another OTP.');
  }
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(challenge.loginEmail || challenge.email, 'Login', otpCode);
  if (!sent) throw new Error('Unable to resend OTP right now. Please try again.');
  pendingLoginOtpChallenges.set(token, {
    ...challenge,
    otpHash: hashOtp(otpCode),
    expiresAt: nowMs() + OTP_EXPIRY_MS,
    requestedAt: nowMs(),
  });
  return { maskedEmail: maskEmailAddress(challenge.loginEmail || challenge.email) };
}

async function createPasswordResetChallenge(c: Context, userRow: Record<string, unknown>) {
  cleanupExpiredChallengeMap(pendingPasswordResetChallenges);
  const email = String(userRow.email || '').trim().toLowerCase();
  const loginEmail = getUserLoginEmail(userRow);
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(loginEmail, 'Password Reset', otpCode);
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
  return { maskedEmail: maskEmailAddress(loginEmail) };
}

async function createSelfResetOtpChallenge(c: Context, authUser: ReturnType<typeof toAuthUser>) {
  cleanupExpiredChallengeMap(pendingSelfResetOtpChallenges);
  const existingToken = getCookie(c, SELF_RESET_OTP_COOKIE) || '';
  const existing = existingToken ? pendingSelfResetOtpChallenges.get(existingToken) : null;
  if (existing && nowMs() - Number(existing.requestedAt || 0) < OTP_RESEND_THROTTLE_MS) {
    throw new Error('Please wait 30 seconds before requesting another OTP.');
  }
  const otpCode = generateOtpCode();
  const sent = await sendOtpEmail(String(authUser.login_email || authUser.email || '').trim().toLowerCase(), 'Password Reset', otpCode);
  if (!sent) throw new Error('Unable to send OTP. Check SMTP configuration and try again.');
  const token = existingToken || randomUUID();
  pendingSelfResetOtpChallenges.set(token, {
    email: authUser.email,
    otpHash: hashOtp(otpCode),
    expiresAt: nowMs() + OTP_EXPIRY_MS,
    requestedAt: nowMs(),
  });
  setChallengeCookie(c, SELF_RESET_OTP_COOKIE, token);
  return { maskedEmail: maskEmailAddress(String(authUser.login_email || authUser.email || '').trim().toLowerCase()) };
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

function getManagedUserAllowedDomain() {
  return String(getAppConfig().google_oauth_allowed_domain || 'rmkcet.ac.in').trim().toLowerCase().replace(/^@/, '') || 'rmkcet.ac.in';
}

function isManagedUserEmailAllowed(email: string) {
  const normalized = String(email || '').trim().toLowerCase();
  const allowedDomain = getManagedUserAllowedDomain();
  return !!normalized && normalized.endsWith(`@${allowedDomain}`);
}

function isLoopbackHost(host: string) {
  const normalized = String(host || '').trim().toLowerCase().replace(/^\[|\]$/g, '');
  return !normalized || normalized === 'localhost' || normalized === '127.0.0.1' || normalized === '::1';
}

function getPublicRequestOrigin(c: Context) {
  const explicitOrigin = String(c.req.header('x-forwarded-origin') || '').trim().replace(/\/+$/, '');
  if (/^https?:\/\//i.test(explicitOrigin)) return explicitOrigin;

  const forwardedProto = String(c.req.header('x-forwarded-proto') || '').split(',')[0]?.trim() || '';
  const forwardedHost = String(c.req.header('x-forwarded-host') || c.req.header('x-original-host') || '').split(',')[0]?.trim() || '';
  if (forwardedProto && forwardedHost) return `${forwardedProto}://${forwardedHost}`;

  const requestUrl = new URL(c.req.url);
  const requestHost = forwardedHost || String(c.req.header('host') || requestUrl.host || '').trim();
  const requestProto = forwardedProto || requestUrl.protocol.replace(/:$/, '') || 'http';
  const fallbackOrigin = `${requestProto}://${requestHost}`;
  const configuredBase = String(getAppConfig().google_oauth_redirect_base_url || '')
    .trim()
    .replace(/\/+$/, '')
    .replace(/\/auth\/google\/callback$/i, '');
  if (/^https?:\/\//i.test(configuredBase) && !isLoopbackHost(new URL(configuredBase).host)) return configuredBase;
  if (!isLoopbackHost(requestHost)) return fallbackOrigin;

  const configuredClientOrigin = [CLIENT_ORIGIN, ...CLIENT_ORIGINS]
    .map((value) => String(value || '').trim().replace(/\/+$/, ''))
    .find((value) => /^https?:\/\//i.test(value) && !isLoopbackHost(new URL(value).host));
  if (configuredClientOrigin) return configuredClientOrigin;

  const configuredServerOrigin = String(SERVER_ORIGIN || '').trim().replace(/\/+$/, '');
  if (/^https?:\/\//i.test(configuredServerOrigin) && !isLoopbackHost(new URL(configuredServerOrigin).host)) {
    return configuredServerOrigin;
  }

  return fallbackOrigin;
}

function escapeHtml(value: unknown) {
  return String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function actorCanManageUser(actor: ReturnType<typeof toAuthUser>, target: Record<string, unknown> | null, mode: 'edit' | 'manage') {
  if (!target) return false;
  const targetRole = normalizeUserRole(String(target.role || 'counselor'));
  const targetAccountEmail = String(target.account_email || target.email || '').trim().toLowerCase();
  if (actor.role === 'principal') return false;
  if (actor.role === 'admin') {
    if (mode === 'manage' && targetAccountEmail === actor.email && targetRole === 'admin') return false;
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
    student_list_link: string;
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
      const departmentRaw = getFirst('branchsec', 'branch', 'department', 'branchesec');
      const password = getFirst('password');
      const studentListLink = getFirst('studentlistlink', 'googlesheetlink', 'sheetlink', 'studentlink');

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
        student_list_link: studentListLink,
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

function parseStudentRows(rawRows: unknown[][]) {
  const students: Array<{ reg_no: string; student_name: string; department?: string; parent_phone?: string; parent_email?: string }> = [];
  const normalizeKey = (value: unknown) => String(value || '').trim().toLowerCase().replace(/[^a-z0-9]/g, '');
  let headerRowIndex = -1;
  let headers: string[] = [];

  for (let rowIndex = 0; rowIndex < rawRows.length; rowIndex += 1) {
    const row = Array.isArray(rawRows[rowIndex]) ? rawRows[rowIndex] : [];
    const normalized = row.map((cell) => normalizeKey(cell));
    const hasRollHeader = normalized.some((value) => ['rno', 'rollno', 'regno', 'registernumber'].includes(value));
    const hasNameHeader = normalized.some((value) => ['name', 'studentname'].includes(value));
    if (hasRollHeader && hasNameHeader) {
      headerRowIndex = rowIndex;
      headers = row.map((cell) => normalizeKey(cell));
      break;
    }
  }

  if (headerRowIndex < 0 || !headers.length) {
    return students;
  }

  const pick = (row: unknown[], ...candidates: string[]) => {
    for (const candidate of candidates) {
      const headerIndex = headers.findIndex((header) => header === candidate || header.includes(candidate));
      if (headerIndex >= 0) {
        return String(row[headerIndex] ?? '').trim();
      }
    }
    return '';
  };

  for (let rowIndex = headerRowIndex + 1; rowIndex < rawRows.length; rowIndex += 1) {
    const row = Array.isArray(rawRows[rowIndex]) ? rawRows[rowIndex] : [];
    const regNo = pick(row, 'rno', 'regno', 'rollno', 'registernumber');
    const studentName = pick(row, 'studentname', 'name');
    const parentPhone = pick(row, 'wno', 'whatsappnumber', 'whatsappno', 'parentphone', 'phone');
    const parentEmail = pick(row, 'parentemail', 'email');
    const department = pick(row, 'department', 'branch');
    if (!regNo || !studentName) continue;
    students.push({
      reg_no: regNo.replace(/\.0$/, ''),
      student_name: studentName,
      parent_phone: normalizePhone(parentPhone) || parentPhone,
      parent_email: parentEmail,
      department: String(department || '').trim().toUpperCase(),
    });
  }

  return students;
}

function parseStudentWorkbook(buffer: Buffer) {
  const workbook = XLSX.read(buffer, { type: 'buffer' });
  const students: Array<{ reg_no: string; student_name: string; department?: string; parent_phone?: string; parent_email?: string }> = [];

  for (const sheetName of workbook.SheetNames) {
    const sheet = workbook.Sheets[sheetName];
    if (!sheet) continue;
    const rows = XLSX.utils.sheet_to_json<unknown[]>(sheet, { header: 1, defval: '', raw: false });
    students.push(...parseStudentRows(rows));
  }
  return students;
}

async function downloadGoogleSheetWorkbook(sheetUrl: string) {
  const match = String(sheetUrl || '').match(/\/d\/([a-zA-Z0-9-_]+)/);
  if (!match) {
    throw new Error('Invalid Google Sheet URL in bulk counselor upload.');
  }
  const exportUrl = `https://docs.google.com/spreadsheets/d/${match[1]}/export?format=xlsx`;
  const response = await fetch(exportUrl, {
    headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)' },
  });
  if (!response.ok) {
    throw new Error('Student list sheet download failed. Ensure the linked sheet is shared as "Anyone with link can view".');
  }
  return Buffer.from(await response.arrayBuffer());
}

function sessionCookieMaxAge(appConfig: Record<string, string>) {
  const timeoutSeconds = Number(appConfig.session_timeout || 86400);
  return Number.isFinite(timeoutSeconds) && timeoutSeconds > 300 ? timeoutSeconds : 86400;
}

function sessionCookieExpires(appConfig: Record<string, string>) {
  return new Date(Date.now() + sessionCookieMaxAge(appConfig) * 1000);
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

function normalizeRegNo(value: unknown) {
  if (typeof value === 'number' && Number.isFinite(value)) {
    return Math.trunc(value).toString().toUpperCase();
  }
  let reg = String(value ?? '').trim().replace(/\s+/g, '').replace(/,/g, '');
  if (!reg) return '';
  if (/^\d+(?:\.\d+)?e[+-]?\d+$/i.test(reg)) {
    const parsed = Number(reg);
    if (Number.isFinite(parsed)) {
      return Math.trunc(parsed).toString().toUpperCase();
    }
  }
  if (reg.endsWith('.0')) reg = reg.slice(0, -2);
  return reg.toUpperCase();
}

function normalizePhone(value: string) {
  const raw = String(value || '').trim();
  if (!raw) return '';
  const hasInternationalPrefix = raw.startsWith('+') || raw.startsWith('00');
  let digits = raw.replace(/\D/g, '');
  if (raw.startsWith('00')) digits = digits.slice(2);
  if (!digits) return '';
  if (hasInternationalPrefix) {
    return digits.length >= 8 && digits.length <= 15 ? `+${digits}` : '';
  }
  if (digits.length >= 8 && digits.length <= 10) return digits;
  if (digits.length > 10 && digits.length <= 15) return `+${digits}`;
  return '';
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

function buildNoticeAttachmentLink(c: Context, publicToken: string) {
  const token = String(publicToken || '').trim();
  if (!token) return '';
  return `${getPublicRequestOrigin(c)}/api/notice-files/${token}`;
}

function buildNoticeAttachmentLinksText(
  c: Context,
  attachments: Array<{ public_token?: string }>,
) {
  return attachments
    .map((attachment) => buildNoticeAttachmentLink(c, String(attachment.public_token || '')))
    .filter(Boolean)
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

type CdpClassStatus = {
  label: string;
  total_date_cols: number;
  filled_cols: number;
  completion_pct: number;
  today_col_exists: boolean;
  today_col_filled: boolean;
  pending_dates: string[];
  missing_entry_count: number;
};

type CdpFacultyStatus = {
  faculty_name: string;
  class_sections: string[];
  status: 'ready' | 'pending' | 'error';
  filled_cols: number;
  total_date_cols: number;
  completion_pct: number;
  pending_class_count: number;
  pending_dates: string[];
  pending_classes: string[];
  missing_entry_count: number;
  class_breakdown: Array<{
    class_label: string;
    filled_cols: number;
    total_date_cols: number;
    completion_pct: number;
    pending_dates: string[];
    missing_entry_count: number;
  }>;
  notes: string[];
};

type CdpSnapshotSummaryStatus = 'ready' | 'pending' | 'error' | 'unparsed';

type CdpSubjectStatus = {
  subject_id: number;
  subject_code: string;
  subject_name: string;
  faculty_name: string;
  department: string;
  year_level: number;
  semester: string;
  classes: CdpClassStatus[];
  faculty_statuses: CdpFacultyStatus[];
  overall_filled_cols: number;
  overall_total_cols: number;
  overall_completion_pct: number;
  today_pending: boolean;
  summary_status: CdpSnapshotSummaryStatus;
  faculty_count: number;
  allocated_class_count: number;
  pending_faculty_count: number;
  pending_class_count: number;
  pending_date_count: number;
  parsed_at: string;
  mark_entry: CdpMarkEntrySnapshot;
};

type CdpMarkEntryTestKey = 'iat1' | 'iat2' | 'model' | 'unit_test';
type CdpMarkEntryStatusValue = 'complete' | 'pending' | 'not_available' | 'error';

type CdpMarkEntryCell = {
  status: CdpMarkEntryStatusValue;
  filled_students: number;
  total_students: number;
  completion_pct: number;
  pending_students: number;
  message: string;
};

type CdpMarkEntryRow = {
  faculty_name: string;
  class_label: string;
  tests: Record<CdpMarkEntryTestKey, CdpMarkEntryCell>;
};

type CdpMarkEntrySummary = {
  key: CdpMarkEntryTestKey;
  label: string;
  status: CdpMarkEntryStatusValue;
  filled_students: number;
  total_students: number;
  completion_pct: number;
  pending_students: number;
  message: string;
};

type CdpMarkEntrySnapshot = {
  summaries: CdpMarkEntrySummary[];
  rows: CdpMarkEntryRow[];
};

type CdpMarkEntryParsedStudentValue = {
  has_value: boolean;
  is_zero: boolean;
};

type CdpAttendanceRoster = {
  label: string;
  normalized_label: string;
  student_reg_nos: string[];
};

const CDP_MARK_ENTRY_TESTS: Array<{ key: CdpMarkEntryTestKey; label: string; aliases: string[] }> = [
  { key: 'iat1', label: 'IAT I', aliases: ['IAT1', 'IAT 1'] },
  { key: 'iat2', label: 'IAT II', aliases: ['IAT2', 'IAT 2'] },
  { key: 'model', label: 'Model', aliases: ['MODEL'] },
  { key: 'unit_test', label: 'Unit Test', aliases: ['UNIT TEST'] },
];
const CDP_MARK_ENTRY_ZERO_PATTERN_THRESHOLD = 0.8;

const CDP_STATUS_CACHE_TTL_MS = 15 * 1000;
const READ_MODEL_CACHE_TTL_MS = 12 * 1000;
const ACTIVITY_DETAIL_CACHE_TTL_MS = 5 * 60 * 1000;
const READ_MODEL_CACHE_MAX_ENTRIES = 250;
const cdpStatusCache = new Map<number, { timestamp: number; data: CdpSubjectStatus }>();
type ReadModelCacheEntry = {
  expiresAt: number;
  payload: unknown;
};
const readModelResponseCache = new Map<string, ReadModelCacheEntry>();
let readModelCacheVersion = 0;

function clearCdpStatusCache(subjectId?: number | null) {
  if (subjectId && Number(subjectId) > 0) {
    cdpStatusCache.delete(Number(subjectId));
    return;
  }
  cdpStatusCache.clear();
}

function cleanupReadModelResponseCache() {
  const now = Date.now();
  for (const [key, entry] of readModelResponseCache.entries()) {
    if (Number(entry.expiresAt || 0) <= now) {
      readModelResponseCache.delete(key);
    }
  }
  if (readModelResponseCache.size <= READ_MODEL_CACHE_MAX_ENTRIES) return;
  const overflow = readModelResponseCache.size - READ_MODEL_CACHE_MAX_ENTRIES;
  let removed = 0;
  for (const key of readModelResponseCache.keys()) {
    readModelResponseCache.delete(key);
    removed += 1;
    if (removed >= overflow) break;
  }
}

function bumpReadModelCacheVersion() {
  readModelCacheVersion += 1;
  if (readModelResponseCache.size > READ_MODEL_CACHE_MAX_ENTRIES / 2) {
    readModelResponseCache.clear();
  }
}

function buildReadModelActorCacheKey(authUser: { email: string; role: string; scopes?: Array<{ department: string; year_level: number }> }) {
  const scopeKey = Array.from(
    new Set(
      (authUser.scopes || [])
        .map((scope) => `${String(scope.department || '').trim().toUpperCase()}::${Number(scope.year_level || 0) || 0}`),
    ),
  )
    .sort((a, b) => a.localeCompare(b))
    .join('|');
  return [
    String(authUser.email || '').trim().toLowerCase(),
    String(authUser.role || '').trim().toLowerCase(),
    scopeKey,
  ].join('::');
}

async function getCachedReadModelPayload<T>(
  bucket: string,
  authUser: { email: string; role: string; scopes?: Array<{ department: string; year_level: number }> },
  queryKey: string,
  producer: () => Promise<T> | T,
  ttlMs = READ_MODEL_CACHE_TTL_MS,
) {
  cleanupReadModelResponseCache();
  const cacheKey = [
    bucket,
    `v${readModelCacheVersion}`,
    buildReadModelActorCacheKey(authUser),
    queryKey,
  ].join('||');
  const cached = readModelResponseCache.get(cacheKey);
  if (cached && Number(cached.expiresAt || 0) > Date.now()) {
    return cached.payload as T;
  }
  const payload = await producer();
  readModelResponseCache.set(cacheKey, {
    expiresAt: Date.now() + ttlMs,
    payload,
  });
  return payload;
}

function normalizeSheetDateLabel(value: string) {
  const [day, month] = String(value || '').split('/').map(Number);
  if (!day || !month) return '';
  return `${String(day).padStart(2, '0')}/${String(month).padStart(2, '0')}`;
}

function getXmlAttributeValue(tagSource: string, attribute: string) {
  const match = String(tagSource || '').match(new RegExp(`${attribute}="([^"]*)"`, 'i'));
  return match ? match[1] : '';
}

function isRedStyleColor(value: string) {
  const normalized = String(value || '').replace(/[^0-9a-f]/gi, '').toUpperCase();
  return normalized.endsWith('FF0000');
}

function parseRedStyleIndexes(stylesXml: string) {
  const fillBlocks = stylesXml.match(/<fill\b[\s\S]*?<\/fill>/gi) || [];
  const fontBlocks = stylesXml.match(/<font\b[\s\S]*?<\/font>/gi) || [];
  const redFillIndexes = new Set<number>();
  const redFontIndexes = new Set<number>();

  fillBlocks.forEach((block, index) => {
    const fgColorMatch = block.match(/<fgColor\b[^>]*rgb="([^"]+)"/i);
    const bgColorMatch = block.match(/<bgColor\b[^>]*rgb="([^"]+)"/i);
    if (isRedStyleColor(fgColorMatch?.[1] || '') || isRedStyleColor(bgColorMatch?.[1] || '')) {
      redFillIndexes.add(index);
    }
  });

  fontBlocks.forEach((block, index) => {
    const colorMatch = block.match(/<color\b[^>]*rgb="([^"]+)"/i);
    if (isRedStyleColor(colorMatch?.[1] || '')) {
      redFontIndexes.add(index);
    }
  });

  const cellXfsBlock = stylesXml.match(/<cellXfs\b[^>]*>([\s\S]*?)<\/cellXfs>/i)?.[1] || '';
  const xfBlocks = cellXfsBlock.match(/<xf\b[^>]*\/>|<xf\b[\s\S]*?<\/xf>/gi) || [];
  const redStyleIndexes = new Set<number>();

  xfBlocks.forEach((block, index) => {
    const fillId = Number(getXmlAttributeValue(block, 'fillId') || -1);
    const fontId = Number(getXmlAttributeValue(block, 'fontId') || -1);
    if (redFillIndexes.has(fillId) || redFontIndexes.has(fontId)) {
      redStyleIndexes.add(index);
    }
  });

  return redStyleIndexes;
}

function resolveWorksheetXmlPath(workbookXml: string, relationshipsXml: string, sheetName: string) {
  const sheets = Array.from(workbookXml.matchAll(/<sheet\b[^>]*name="([^"]+)"[^>]*r:id="([^"]+)"/gi))
    .map((match) => ({ name: match[1], relId: match[2] }));
  const targetSheet = sheets.find((entry) => entry.name === sheetName);
  if (!targetSheet) return '';

  const relation = Array.from(relationshipsXml.matchAll(/<Relationship\b[^>]*Id="([^"]+)"[^>]*Target="([^"]+)"/gi))
    .map((match) => ({ id: match[1], target: match[2] }))
    .find((entry) => entry.id === targetSheet.relId);
  if (!relation) return '';

  const targetPath = relation.target.replace(/\\/g, '/').replace(/^\/+/, '');
  return targetPath.startsWith('xl/') ? targetPath : `xl/${targetPath}`;
}

async function extractUnavailableStudentRowsFromWorkbook(workbookBuffer: Buffer, sheetName: string) {
  try {
    const zip = await JSZip.loadAsync(workbookBuffer);
    const stylesXml = await zip.file('xl/styles.xml')?.async('string');
    const workbookXml = await zip.file('xl/workbook.xml')?.async('string');
    const relationshipsXml = await zip.file('xl/_rels/workbook.xml.rels')?.async('string');
    if (!stylesXml || !workbookXml || !relationshipsXml) return new Set<number>();

    const redStyleIndexes = parseRedStyleIndexes(stylesXml);
    if (!redStyleIndexes.size) return new Set<number>();

    const worksheetPath = resolveWorksheetXmlPath(workbookXml, relationshipsXml, sheetName);
    if (!worksheetPath) return new Set<number>();

    const worksheetXml = await zip.file(worksheetPath)?.async('string');
    if (!worksheetXml) return new Set<number>();

    const unavailableRows = new Set<number>();
    const cellMatches = worksheetXml.matchAll(/<c\b([^>]*)\br="([A-Z]+)(\d+)"([^>]*)/gi);
    for (const match of cellMatches) {
      const attrs = `${match[1] || ''} ${match[4] || ''}`;
      const styleIndex = Number(getXmlAttributeValue(attrs, 's') || -1);
      if (!redStyleIndexes.has(styleIndex)) continue;
      const column = String(match[2] || '').toUpperCase();
      if (!['A', 'B', 'C', 'D'].includes(column)) continue;
      unavailableRows.add(Number(match[3] || 0));
    }

    return unavailableRows;
  } catch {
    return new Set<number>();
  }
}

function getTodaySheetLabel() {
  const now = new Date();
  return `${String(now.getDate()).padStart(2, '0')}/${String(now.getMonth() + 1).padStart(2, '0')}`;
}

function isAttendanceStudentRow(row: unknown[]) {
  if (!Array.isArray(row)) return false;
  const serial = Number(row[0]);
  const regNo = normalizeRegNo(row[1]);
  const name = String(row[2] ?? '').trim();
  return Number.isFinite(serial) && serial >= 1 && serial <= 200 && /^\d{10,15}$/.test(regNo) && !!name;
}

function getAttendanceHeaderPreview(row: unknown[]) {
  if (!Array.isArray(row)) return '';
  return row
    .slice(0, 4)
    .map((value) => String(value ?? '').trim().toLowerCase())
    .filter(Boolean)
    .join(' ');
}

function looksLikeAttendanceDateHeader(row: unknown[], nextRow?: unknown[]) {
  const headerPreview = getAttendanceHeaderPreview(row);
  const nextPreview = Array.isArray(nextRow) ? getAttendanceHeaderPreview(nextRow) : '';
  const hasPrimaryMarker =
    headerPreview.includes('register number')
    || headerPreview.includes('date')
    || headerPreview.includes('s.no')
    || headerPreview.includes('s no');
  const hasSupportMarker =
    nextPreview.includes('period')
    || nextPreview.includes('name of the student');
  return hasPrimaryMarker || hasSupportMarker;
}

function withReadModelMeta<T extends Record<string, unknown>>(payload: T) {
  return {
    ...payload,
    cacheMeta: {
      version: readModelCacheVersion,
      generatedAt: new Date().toISOString(),
    },
  };
}

function buildReportsOverviewPayload(
  authUser: ReturnType<typeof toAuthUser>,
  filterDept: string,
  filterYearLevel: number | null,
) {
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

  return withReadModelMeta({
    departments: visibleDepartments,
    selectedDepartment: resolvedDepartment,
    availableYears,
    selectedYear,
    showDepartmentPicker: !resolvedDepartment,
    showYearPicker: !!resolvedDepartment && !selectedYear,
    tests,
  });
}

async function buildCdpOverviewPayload(
  authUser: ReturnType<typeof toAuthUser>,
  options: {
    requestedDepartment: string;
    requestedYear: number | null;
    requestedSemester: string;
    requestedSubjectId: number | null;
  },
) {
  const { requestedDepartment, requestedYear, requestedSemester } = options;
  const departments = getVisibleDepartmentsForActor(authUser);
  const yearsByDepartment = getScopedYearsByDepartment(authUser);
  const visibleSubjects = listSubjectsForActor(authUser);
  const availableSemesters = ['1', '2'];

  const selectedDepartment =
    requestedDepartment && departments.some((department) => department.code.toUpperCase() === requestedDepartment)
      ? requestedDepartment
      : (departments.length === 1 ? departments[0].code.toUpperCase() : '');
  const availableYears = selectedDepartment
    ? Array.from(new Set(yearsByDepartment.get(selectedDepartment) || [])).sort((a, b) => a - b)
    : [];
  const selectedYear =
    requestedYear && availableYears.includes(requestedYear)
      ? requestedYear
      : (availableYears.length === 1 ? availableYears[0] : null);
  const selectedSemester =
    availableSemesters.includes(requestedSemester)
      ? requestedSemester
      : '';
  const scopedSubjects = selectedDepartment && selectedYear && selectedSemester
    ? visibleSubjects.filter((subject) => subject.department === selectedDepartment && subject.year_level === selectedYear && subject.semester === selectedSemester)
    : [];
  const requestedSubjectId = Number(options.requestedSubjectId || 0) || null;
  const selectedSubject = requestedSubjectId
    ? scopedSubjects.find((subject) => subject.id === requestedSubjectId) || null
    : null;
  const snapshotMap = new Map(
    listCdpSubjectSnapshots({ subjectIds: scopedSubjects.map((subject) => subject.id) }).map((snapshot) => [snapshot.subject_id, snapshot]),
  );
  const subjects = scopedSubjects.map((subject) => {
    const snapshot = snapshotMap.get(subject.id) || null;
    return {
      ...subject,
      summary_status: snapshot?.summary_status || 'unparsed',
      faculty_count: snapshot?.faculty_count || subject.faculty_allocations.length || splitFacultyNames(subject.faculty_name || '').length,
      allocated_class_count: snapshot?.allocated_class_count || subject.class_sections.length,
      pending_faculty_count: snapshot?.pending_faculty_count || 0,
      pending_class_count: snapshot?.pending_class_count || 0,
      pending_date_count: snapshot?.pending_date_count || 0,
      parsed_at: snapshot?.parsed_at || null,
      parser_error: snapshot?.parser_error || '',
      faculty_statuses: snapshot?.faculty_statuses || [],
    };
  });
  const selectedSnapshot = selectedSubject ? (snapshotMap.get(selectedSubject.id) || null) : null;
  const selectedSubjectDetail = selectedSubject ? {
    subject_id: selectedSubject.id,
    subject_code: selectedSubject.subject_code,
    subject_name: selectedSubject.subject_name,
    faculty_name: selectedSubject.faculty_name,
    department: selectedSubject.department,
    year_level: selectedSubject.year_level,
    semester: selectedSubject.semester,
    classes: selectedSnapshot?.class_statuses || [],
    faculty_statuses: selectedSnapshot?.faculty_statuses || [],
    overall_filled_cols: (selectedSnapshot?.class_statuses || []).reduce((sum, item) => sum + Number(item.filled_cols || 0), 0),
    overall_total_cols: (selectedSnapshot?.class_statuses || []).reduce((sum, item) => sum + Number(item.total_date_cols || 0), 0),
    overall_completion_pct: (selectedSnapshot?.class_statuses || []).reduce((sum, item) => sum + Number(item.total_date_cols || 0), 0)
      ? Math.round(
        (
          (selectedSnapshot?.class_statuses || []).reduce((sum, item) => sum + Number(item.filled_cols || 0), 0)
          / Math.max(1, (selectedSnapshot?.class_statuses || []).reduce((sum, item) => sum + Number(item.total_date_cols || 0), 0))
        ) * 100,
      )
      : 100,
    today_pending: (selectedSnapshot?.class_statuses || []).some((item) => !!item.today_col_exists && !item.today_col_filled),
    summary_status: selectedSnapshot?.summary_status || 'unparsed',
    faculty_count: selectedSnapshot?.faculty_count || selectedSubject.faculty_allocations.length || splitFacultyNames(selectedSubject.faculty_name || '').length,
    allocated_class_count: selectedSnapshot?.allocated_class_count || selectedSubject.class_sections.length,
    pending_faculty_count: selectedSnapshot?.pending_faculty_count || 0,
    pending_class_count: selectedSnapshot?.pending_class_count || 0,
    pending_date_count: selectedSnapshot?.pending_date_count || 0,
    parsed_at: selectedSnapshot?.parsed_at || null,
    parser_error: selectedSnapshot?.parser_error || '',
    mark_entry: selectedSnapshot?.mark_entry_statuses || { summaries: [], rows: [] },
  } : null;

  const scopeKeys = new Set(visibleSubjects.map((subject) => `${subject.department}::${subject.year_level}`));
  const departmentsCovered = new Set(visibleSubjects.map((subject) => subject.department)).size;
  const yearsCovered = new Set(visibleSubjects.map((subject) => String(subject.year_level))).size;

  return withReadModelMeta({
    summary: {
      total_subjects: visibleSubjects.length,
      configured_sheets: visibleSubjects.filter((subject) => !!String(subject.google_sheet_link || '').trim()).length,
      departments_covered: departmentsCovered,
      years_covered: yearsCovered,
      scopes_covered: scopeKeys.size,
    },
    departments,
    selectedDepartment,
    availableYears,
    selectedYear,
    availableSemesters,
    selectedSemester,
    showDepartmentPicker: !selectedDepartment,
    showYearPicker: !!selectedDepartment && !selectedYear,
    showSemesterPicker: !!selectedDepartment && !!selectedYear && !selectedSemester,
    subjects,
    selectedSubjectId: selectedSubject?.id || null,
    selectedSubject,
    selectedSubjectDetail,
    scopeSnapshot: selectedDepartment && selectedYear ? getSubjectScopeSnapshot(selectedDepartment, selectedYear) : null,
  });
}

function buildActivityOverviewPayload(
  authUser: {
    role: string;
    email: string;
    name: string;
    department: string | null;
    year_level?: number | null;
    scopes: Array<{ department: string; year_level: number }>;
  },
  options: {
    selectedDepartment?: string;
    selectedYear?: number | null;
    selectedSemester?: string;
    selectedTestName?: string;
    searchQuery?: string;
    sortMode?: string;
  },
) {
  const selectedDepartment = String(options.selectedDepartment || '').trim().toUpperCase();
  const selectedYear = Number(options.selectedYear || 0) || null;
  const selectedSemester = String(options.selectedSemester || '').trim();
  const selectedTestName = String(options.selectedTestName || '').trim().toUpperCase();
  const searchQuery = String(options.searchQuery || '').trim();
  const sortMode = String(options.sortMode || 'pending_first').trim() || 'pending_first';

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
  const allowedScopes = getAllowedScopesForUser(authUser as ReturnType<typeof toAuthUser>);
  const tests = departmentCode && yearLevel
    ? getAllUniqueTests({ filterDept: departmentCode, filterYearLevel: yearLevel, allowedScopes })
    : [];
  const scopeSnapshot = departmentCode && yearLevel
    ? getCounselorActivityScopeSnapshot(
      departmentCode,
      yearLevel,
      tests.map((test) => ({
        test_id: test.test_id,
        department: test.department,
        year_level: test.year_level,
        semester: test.semester,
        test_name: test.test_name,
      })),
    )
    : null;
  const activityTestStatus = scopeSnapshot?.test_status || {
    '1': { 'IAT 1': false, 'IAT 2': false, 'MODEL EXAM': false },
    '2': { 'IAT 1': false, 'IAT 2': false, 'MODEL EXAM': false },
  };

  const selectionReady = !!(departmentCode && yearLevel && ['1', '2'].includes(selectedSemester) && selectedTestName);
  const prefetchedResults = scopeSnapshot?.results || [];
  const prefetchedMatch = selectionReady
    ? prefetchedResults.find((item) => item.semester === selectedSemester && item.test_name === selectedTestName) || null
    : null;
  const result = selectionReady
    ? (prefetchedMatch && !searchQuery && sortMode === 'pending_first'
      ? prefetchedMatch
      : getCounselorActivityForTest(departmentCode, yearLevel!, selectedSemester, selectedTestName, searchQuery, sortMode))
    : null;

  return withReadModelMeta({
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
    prefetchedResults,
    result,
  });
}

function splitFacultyNames(raw: string) {
  return Array.from(new Set(
    String(raw || '')
      .split(/(?:\r?\n|\/|;)+/g)
      .map((value) => String(value || '').trim())
      .filter(Boolean),
  ));
}

function canonicalizeDepartmentCode(raw: string) {
  const normalized = String(raw || '')
    .trim()
    .toUpperCase()
    .replace(/\s+/g, ' ');
  if (!normalized) return '';
  const compact = normalized.replace(/[^A-Z0-9]/g, '');
  if (compact === 'EEV' || compact === 'EEVLSI' || compact === 'EEVLSIDESIGNANDTECHNOLOGY') {
    return 'EE(VLSI)';
  }
  return normalized;
}

function normalizeParsedClassLabel(raw: string, fallbackDepartment = '') {
  const text = String(raw || '')
    .trim()
    .toUpperCase()
    .replace(/\s*-\s*/g, ' ')
    .replace(/\s+/g, ' ');
  if (!text) return '';
  if (/^[A-F]$/.test(text)) {
    const department = canonicalizeDepartmentCode(fallbackDepartment);
    return department ? `${department} ${text}` : text;
  }
  const directMatch = text.match(/^([A-Z0-9()&/]+)\s+([A-F])$/);
  if (directMatch) {
    return `${canonicalizeDepartmentCode(directMatch[1]) || directMatch[1]} ${directMatch[2]}`.trim();
  }
  return text;
}

function isDepartmentClassLabel(raw: string, expectedDepartment = '') {
  const normalized = normalizeParsedClassLabel(raw, expectedDepartment);
  if (!normalized) return false;
  const directMatch = normalized.match(/^(.+?)\s+([A-F])$/);
  if (!directMatch) {
    return /^[A-F]$/.test(String(raw || '').trim().toUpperCase());
  }
  if (!expectedDepartment) return true;
  return doesParsedDepartmentMatch(expectedDepartment, directMatch[1]);
}

function keepLeadingContiguousDateColumns<T extends { colIndex: number }>(columns: T[]) {
  const contiguous: T[] = [];
  let previousColIndex = -1;
  for (const column of columns) {
    const colIndex = Number(column?.colIndex);
    if (!Number.isFinite(colIndex)) continue;
    if (!contiguous.length) {
      contiguous.push(column);
      previousColIndex = colIndex;
      continue;
    }
    if (colIndex !== previousColIndex + 1) {
      break;
    }
    contiguous.push(column);
    previousColIndex = colIndex;
  }
  return contiguous;
}

function extractClassLabelsFromText(raw: string, fallbackDepartment = '') {
  const text = String(raw || '')
    .trim()
    .toUpperCase()
    .replace(/\s+/g, ' ');
  if (!text) return [] as string[];

  const groupedMatch = text.match(/^([A-Z0-9()&/]+)\s*-\s*([A-F](?:\s*,\s*[A-F])+)$/
  );
  if (groupedMatch) {
    return groupedMatch[2]
      .split(',')
      .map((entry) => `${groupedMatch[1]} ${String(entry || '').trim()}`)
      .map((entry) => normalizeParsedClassLabel(entry, fallbackDepartment))
      .filter(Boolean);
  }

  return Array.from(new Set(
    text
      .split(/[;,/]+/g)
      .map((entry) => normalizeParsedClassLabel(entry, fallbackDepartment))
      .filter((entry) => /^[A-Z0-9()&/]+(?:\s+[A-F])?$/.test(entry)),
  ));
}

function doClassSectionsMatchDepartment(classSections: string[], department: string) {
  const normalizedDepartment = canonicalizeDepartmentCode(department);
  if (!normalizedDepartment) return true;
  const sections = Array.from(new Set(
    (classSections || [])
      .map((value) => normalizeParsedClassLabel(String(value || '').trim(), normalizedDepartment))
      .filter(Boolean),
  ));
  if (!sections.length) return true;
  return sections.every((section) => section === normalizedDepartment || section.startsWith(`${normalizedDepartment} `));
}

function normalizeDepartmentComparisonToken(value: string) {
  return canonicalizeDepartmentCode(value).replace(/[^A-Z0-9]/g, '');
}

function doesParsedDepartmentMatch(expectedDepartment: string, candidateDepartment: string) {
  const expected = normalizeDepartmentComparisonToken(expectedDepartment);
  const candidate = normalizeDepartmentComparisonToken(candidateDepartment);
  if (!expected || !candidate) return true;
  return expected === candidate;
}

function parseSheetDateToken(
  value: unknown,
  subject?: { academic_start_year?: number | null; academic_end_year?: number | null },
  cell?: XLSX.CellObject,
) {
  const now = new Date();
  const startYear = Number(subject?.academic_start_year || 0) || now.getFullYear();
  const rawEndYear = Number(subject?.academic_end_year || startYear + 1) || (startYear + 1);
  const endYear =
    rawEndYear >= startYear && rawEndYear <= startYear + 1
      ? rawEndYear
      : (startYear + 1);
  const resolveAcademicYear = (month: number) => (month >= 6 ? startYear : endYear);
  const raw = String(cell?.w ?? value ?? '').trim();
  if (!raw) return null;

  const shortMatch = raw.match(/^(\d{1,2})[\/\-](\d{1,2})$/);
  if (shortMatch) {
    const day = Number(shortMatch[1]);
    const month = Number(shortMatch[2]);
    if (day >= 1 && day <= 31 && month >= 1 && month <= 12) {
      return new Date(resolveAcademicYear(month), month - 1, day);
    }
  }

  const longMatch = raw.match(/^(\d{1,2})[\/\-](\d{1,2})[\/\-](\d{2,4})$/);
  if (longMatch) {
    const day = Number(longMatch[1]);
    const month = Number(longMatch[2]);
    let year = Number(longMatch[3]);
    if (year < 100) year += 2000;
    if (day >= 1 && day <= 31 && month >= 1 && month <= 12) {
      return new Date(year || resolveAcademicYear(month), month - 1, day);
    }
  }

  if (typeof value === 'number' && value > 40000 && value < 60000) {
    const date = new Date(Math.round((value - 25569) * 86400 * 1000));
    date.setFullYear(resolveAcademicYear(date.getMonth() + 1));
    return date;
  }

  if (/^\d+(?:\.\d+)?$/.test(raw)) {
    return null;
  }

  const parsed = Date.parse(raw);
  if (Number.isFinite(parsed)) {
    const date = new Date(parsed);
    date.setFullYear(resolveAcademicYear(date.getMonth() + 1));
    return date;
  }

  return null;
}

function parseFacultyAllocationsFromWorkbook(workbook: XLSX.WorkBook, fallbackDepartment = '', allowedClasses: string[] = []) {
  const allowed = new Set((allowedClasses || []).map((entry) => String(entry || '').trim().toUpperCase()).filter(Boolean));
  const facultyClassMap = new Map<string, Set<string>>();

  const findNextValue = (row: unknown[], startIndex: number) => {
    for (let index = startIndex + 1; index < row.length; index += 1) {
      const value = String(row[index] ?? '').trim();
      if (value) return value;
    }
    return '';
  };

  const addAllocation = (facultyName: string, classes: string[]) => {
    const normalizedFaculty = String(facultyName || '').trim();
    const normalizedClasses = classes
      .map((entry) => normalizeParsedClassLabel(entry, fallbackDepartment))
      .filter(Boolean)
      .filter((entry) => !allowed.size || allowed.has(entry));
    if (!normalizedFaculty || !normalizedClasses.length) return;
    if (!facultyClassMap.has(normalizedFaculty)) {
      facultyClassMap.set(normalizedFaculty, new Set());
    }
    const classSet = facultyClassMap.get(normalizedFaculty)!;
    normalizedClasses.forEach((entry) => classSet.add(entry));
  };

  const candidateSheetNames = workbook.SheetNames.filter((name) => {
    const lower = String(name || '').trim().toLowerCase();
    return lower.includes('proposed lecture plan') || lower === 'second page';
  });

  for (const sheetName of candidateSheetNames) {
    const sheet = workbook.Sheets[sheetName];
    if (!sheet) continue;
    const rows = XLSX.utils.sheet_to_json<unknown[]>(sheet, { header: 1, defval: '' });
    const isSecondPage = String(sheetName || '').trim().toLowerCase() === 'second page';
    let recentFaculty: { names: string[]; rowIndex: number } | null = null;
    let recentClasses: { classes: string[]; rowIndex: number } | null = null;

    const tryAssociate = () => {
      if (!recentFaculty || !recentClasses) return;
      if (Math.abs(recentFaculty.rowIndex - recentClasses.rowIndex) > 8) return;
      if (isSecondPage && recentFaculty.names.length > 1 && recentClasses.classes.length === 1) return;
      recentFaculty.names.forEach((name) => addAllocation(name, recentClasses!.classes));
    };

    for (let rowIndex = 0; rowIndex < rows.length; rowIndex += 1) {
      const row = Array.isArray(rows[rowIndex]) ? rows[rowIndex] : [];
      for (let colIndex = 0; colIndex < row.length; colIndex += 1) {
        const cellText = String(row[colIndex] ?? '').trim().toLowerCase();
        if (!cellText) continue;
        if (
          cellText.includes('name of the faculty')
          || cellText.includes('name of faculty')
          || cellText.includes('name of the faculty member')
        ) {
          const names = splitFacultyNames(findNextValue(row, colIndex));
          if (names.length) {
            recentFaculty = { names, rowIndex };
            tryAssociate();
          }
        } else if (cellText === 'branch' || cellText.startsWith('branch:')) {
          const classes = extractClassLabelsFromText(findNextValue(row, colIndex), fallbackDepartment);
          if (classes.length) {
            recentClasses = { classes, rowIndex };
            tryAssociate();
          }
        }
      }
    }
  }

  return Array.from(facultyClassMap.entries()).map(([faculty_name, classSet]) => ({
    faculty_name,
    class_sections: Array.from(classSet),
  }));
}

async function parseGoogleSheetMetadata(url: string, fallbackDepartment = '') {
  const match = String(url || '').match(/\/d\/([a-zA-Z0-9-_]+)/);
  if (!match) {
    throw new Error('Invalid Google Sheet URL format.');
  }

  const exportUrl = `https://docs.google.com/spreadsheets/d/${match[1]}/export?format=xlsx`;
  const response = await fetch(exportUrl, {
    headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)' },
  });
  if (!response.ok) {
    throw new Error('Google Sheet download failed. Ensure the sheet is shared as "Anyone with link can view".');
  }

  const workbook = XLSX.read(await response.arrayBuffer(), { type: 'array' });
  let sheet = workbook.Sheets['First Page'] || workbook.Sheets['Second Page'];
  if (!sheet && workbook.SheetNames.length) {
    sheet = workbook.Sheets[workbook.SheetNames[0]];
  }
  if (!sheet) {
    throw new Error('The workbook contains no readable sheets.');
  }

  const rows = XLSX.utils.sheet_to_json<unknown[]>(sheet, { header: 1 });
  let faculty_name = '';
  let subject_code = '';
  let subject_name = '';

  const cleanValue = (value: unknown) => String(value ?? '').trim().replace(/\n/g, ' ');
  const findNextValue = (row: unknown[], startIndex: number) => {
    for (let index = startIndex + 1; index < row.length; index += 1) {
      const value = cleanValue(row[index]);
      if (value) return value;
    }
    return '';
  };

  for (const row of rows) {
    if (!Array.isArray(row)) continue;
    for (let columnIndex = 0; columnIndex < row.length; columnIndex += 1) {
      const cell = row[columnIndex];
      const cellText = String(cell ?? '').trim().toLowerCase();
      if (!cellText) continue;

      if (!faculty_name && (
        cellText.includes('faculty member')
        || cellText.includes('name of the faculty')
        || cellText.includes('name of faculty')
      )) {
        faculty_name = findNextValue(row, columnIndex);
      } else if (!subject_code && (cellText.includes('course code') || cellText.includes('subject code'))) {
        subject_code = findNextValue(row, columnIndex);
      } else if (!subject_name && (
        cellText.includes('name of the course')
        || cellText.includes('course name')
        || cellText.includes('subject name')
      )) {
        subject_name = findNextValue(row, columnIndex);
      }
    }
  }

  const parsedClassSections: string[] = [];
  const attendanceSheetName =
    workbook.SheetNames.find((name) => name.toLowerCase().replace(/_/g, ' ').includes('daily attendance'))
    || workbook.SheetNames.find((name) => name.toLowerCase().includes('attendance'))
    || '';

  if (attendanceSheetName) {
    const attendanceSheet = workbook.Sheets[attendanceSheetName];
    const attendanceRows = XLSX.utils.sheet_to_json<unknown[]>(attendanceSheet, { header: 1, defval: null, raw: true });
    const boundaryRows: number[] = [];

    for (let rowIndex = 0; rowIndex < attendanceRows.length; rowIndex += 1) {
      const row = attendanceRows[rowIndex];
      if (!Array.isArray(row)) continue;
      const text = row.map((cell) => String(cell ?? '')).join(' ').toLowerCase();
      if (
        text.includes('rmkcet')
        || text.includes('r.m.k.c.e.t')
        || text.includes('rmk')
        || text.includes('college of engineering')
      ) {
        const last = boundaryRows[boundaryRows.length - 1];
        if (last === undefined || rowIndex - last > 3) boundaryRows.push(rowIndex);
      }
    }

    const sections = (boundaryRows.length ? boundaryRows : [0]).map((startRow, index, source) => ({
      startRow,
      endRow: source[index + 1] !== undefined ? source[index + 1] - 1 : attendanceRows.length - 1,
    }));
    const validSections: Array<{ detectedClass: string }> = [];

    for (const section of sections) {
      const sectionRows = attendanceRows.slice(section.startRow, section.endRow + 1);
      let detectedClass = '';
      let bestDateHeaderIndex = -1;
      let bestDateCount = 0;

      for (let localRowIndex = 0; localRowIndex < Math.min(sectionRows.length, 18); localRowIndex += 1) {
        const row = sectionRows[localRowIndex];
        if (!Array.isArray(row)) continue;
        let dateCount = 0;
      for (let colIndex = 0; colIndex < row.length; colIndex += 1) {
        const cellKey = XLSX.utils.encode_cell({ r: section.startRow + localRowIndex, c: colIndex });
        const cell = attendanceSheet[cellKey];
        if (parseSheetDateToken(row[colIndex], undefined, cell)) {
          dateCount += 1;
        }
      }
      if (dateCount >= 3) {
        let contiguousDateCount = 0;
        let previousDateCol = -1;
        for (let colIndex = 0; colIndex < row.length; colIndex += 1) {
          const cellKey = XLSX.utils.encode_cell({ r: section.startRow + localRowIndex, c: colIndex });
          const cell = attendanceSheet[cellKey];
          if (!parseSheetDateToken(row[colIndex], undefined, cell)) continue;
          if (previousDateCol !== -1 && colIndex !== previousDateCol + 1) break;
          contiguousDateCount += 1;
          previousDateCol = colIndex;
        }
        dateCount = contiguousDateCount;
      }
      if (dateCount > bestDateCount && looksLikeAttendanceDateHeader(row, sectionRows[localRowIndex + 1])) {
        bestDateCount = dateCount;
        bestDateHeaderIndex = localRowIndex;
      }
    }

      const hasRealStudents = sectionRows.some((row) => Array.isArray(row) && isAttendanceStudentRow(row));
      if (bestDateHeaderIndex < 0 || !bestDateCount || !hasRealStudents) {
        continue;
      }

      for (let localRowIndex = 0; localRowIndex < Math.min(bestDateHeaderIndex, sectionRows.length); localRowIndex += 1) {
        const row = sectionRows[localRowIndex];
        if (!Array.isArray(row) || isAttendanceStudentRow(row)) continue;
        const serialToken = String(row[0] ?? '').trim();
        const regToken = String(row[1] ?? '').trim();
        if (/^\d+(\.\d+)?$/.test(serialToken) || /^\d{10,15}(?:\.0+)?$/.test(regToken)) continue;
        const candidate = normalizeParsedClassLabel(String(row[2] ?? '').trim(), fallbackDepartment);
        if (candidate && isDepartmentClassLabel(candidate, fallbackDepartment)) {
          detectedClass = candidate;
          break;
        }
      }

      validSections.push({ detectedClass });
    }

    validSections.forEach((section, index) => {
      let resolvedClass = section.detectedClass;
      if (!resolvedClass) {
        const generatedLabel = ['A', 'B', 'C', 'D', 'E', 'F'][index] || `SECTION ${index + 1}`;
        resolvedClass = generatedLabel;
        if (/^[A-Z]$/.test(resolvedClass) && fallbackDepartment) {
          resolvedClass = `${String(fallbackDepartment || '').trim().toUpperCase()} ${resolvedClass}`;
        }
      }
      if (resolvedClass && !parsedClassSections.includes(resolvedClass)) {
        parsedClassSections.push(resolvedClass);
      }
    });
  }

  const parsedFacultyAllocations = parseFacultyAllocationsFromWorkbook(workbook, fallbackDepartment, parsedClassSections);
  const fallbackFacultyNames = splitFacultyNames(faculty_name);
  const resolvedFacultyAllocations = parsedFacultyAllocations.length
    ? parsedFacultyAllocations
    : (
      fallbackFacultyNames.length === 1 && parsedClassSections.length
        ? [{
          faculty_name: fallbackFacultyNames[0],
          class_sections: parsedClassSections,
        }]
        : []
    );

  return {
    faculty_name,
    faculty_names: splitFacultyNames(faculty_name),
    subject_code,
    subject_name,
    class_sections: parsedClassSections,
    faculty_allocations: resolvedFacultyAllocations,
  };
}

function createCdpMarkEntryCell(
  status: CdpMarkEntryStatusValue,
  filledStudents = 0,
  totalStudents = 0,
  message = '',
): CdpMarkEntryCell {
  const normalizedTotal = Math.max(0, Number(totalStudents || 0));
  const normalizedFilled = Math.max(0, Math.min(normalizedTotal, Number(filledStudents || 0)));
  const pendingStudents = Math.max(0, normalizedTotal - normalizedFilled);
  return {
    status,
    filled_students: normalizedFilled,
    total_students: normalizedTotal,
    completion_pct: normalizedTotal ? Math.round((normalizedFilled / normalizedTotal) * 100) : 0,
    pending_students: pendingStudents,
    message: String(message || '').trim(),
  };
}

function buildCdpMarkEntryErrorSnapshot(message: string): CdpMarkEntrySnapshot {
  return {
    summaries: CDP_MARK_ENTRY_TESTS.map((test) => ({
      key: test.key,
      label: test.label,
      ...createCdpMarkEntryCell('error', 0, 0, message),
    })),
    rows: [],
  };
}

function normalizeWorkbookSheetLookupKey(value: string) {
  return String(value || '').trim().toUpperCase().replace(/[^A-Z0-9]/g, '');
}

function findCdpMarkEntrySheetName(workbook: XLSX.WorkBook, aliases: string[]) {
  const aliasSet = new Set((aliases || []).map(normalizeWorkbookSheetLookupKey));
  return workbook.SheetNames.find((sheetName) => aliasSet.has(normalizeWorkbookSheetLookupKey(sheetName))) || '';
}

function detectCdpMarkEntrySheetColumns(rows: unknown[][]) {
  const inferNameColumn = (headerRowIndex: number, regCol: number) => {
    const candidateCounts = new Map<number, number>();
    for (let rowIndex = headerRowIndex + 1; rowIndex < Math.min(rows.length, headerRowIndex + 18); rowIndex += 1) {
      const row = rows[rowIndex];
      if (!Array.isArray(row)) continue;
      if (!/^\d{10,15}$/.test(normalizeRegNo(row[regCol]))) continue;
      for (let colIndex = regCol + 1; colIndex <= Math.min(row.length - 1, regCol + 3); colIndex += 1) {
        const text = String(row[colIndex] ?? '').trim();
        if (!text || !/[A-Za-z]/.test(text)) continue;
        candidateCounts.set(colIndex, (candidateCounts.get(colIndex) || 0) + 1);
      }
    }
    return Array.from(candidateCounts.entries())
      .sort((a, b) => b[1] - a[1] || a[0] - b[0])[0]?.[0] ?? -1;
  };

  const detectTotalColumnFromHeaders = (headerRowIndex: number, nameCol: number) => {
    const totalCols: number[] = [];
    for (let rowIndex = headerRowIndex; rowIndex < Math.min(rows.length, headerRowIndex + 6); rowIndex += 1) {
      const row = rows[rowIndex];
      if (!Array.isArray(row)) continue;
      for (let colIndex = nameCol + 1; colIndex < row.length; colIndex += 1) {
        const cellText = String(row[colIndex] ?? '').trim().toLowerCase().replace(/\s+/g, ' ');
        if (cellText === 'total') {
          totalCols.push(colIndex);
        }
      }
    }
    return totalCols.length ? Math.max(...totalCols) : -1;
  };

  const inferTotalColumnFromStudentRows = (headerRowIndex: number, regCol: number, nameCol: number) => {
    const rightmostFilledCols: number[] = [];
    for (let rowIndex = headerRowIndex + 1; rowIndex < Math.min(rows.length, headerRowIndex + 30); rowIndex += 1) {
      const row = rows[rowIndex];
      if (!Array.isArray(row)) continue;
      if (!/^\d{10,15}$/.test(normalizeRegNo(row[regCol]))) continue;
      const studentName = String(row[nameCol] ?? '').trim();
      if (!studentName) continue;
      for (let colIndex = row.length - 1; colIndex > nameCol; colIndex -= 1) {
        const text = String(row[colIndex] ?? '').trim();
        if (!text) continue;
        rightmostFilledCols.push(colIndex);
        break;
      }
    }
    return rightmostFilledCols.length ? Math.max(...rightmostFilledCols) : -1;
  };

  for (let rowIndex = 0; rowIndex < Math.min(rows.length, 10); rowIndex += 1) {
    const row = rows[rowIndex];
    if (!Array.isArray(row)) continue;
    let regCol = -1;
    let nameCol = -1;
    for (let colIndex = 0; colIndex < row.length; colIndex += 1) {
      const cellText = String(row[colIndex] ?? '').trim().toLowerCase().replace(/\s+/g, ' ');
      if (!cellText) continue;
      if (regCol < 0 && (cellText.includes('register number') || cellText.includes('register no'))) {
        regCol = colIndex;
      }
      if (
        nameCol < 0
        && (
          cellText.includes('name of the student')
          || cellText.includes('student name')
          || cellText === 'name'
        )
      ) {
        nameCol = colIndex;
      }
    }
    if (regCol < 0) continue;
    if (nameCol < 0) {
      nameCol = inferNameColumn(rowIndex, regCol);
    }
    if (nameCol < 0) continue;
    let totalCol = detectTotalColumnFromHeaders(rowIndex, nameCol);
    if (totalCol < 0) {
      totalCol = inferTotalColumnFromStudentRows(rowIndex, regCol, nameCol);
    }
    if (totalCol > nameCol) {
      return {
        header_row_index: rowIndex,
        reg_col: regCol,
        name_col: nameCol,
        total_col: totalCol,
      };
    }
  }
  return null;
}

function parseCdpMarkEntrySheetData(workbook: XLSX.WorkBook, sheetName: string) {
  const sheet = workbook.Sheets[sheetName];
  if (!sheet) {
    throw new Error('Exam tab is not readable.');
  }
  const rows = XLSX.utils.sheet_to_json<unknown[]>(sheet, { header: 1, defval: null, raw: true });
  const detected = detectCdpMarkEntrySheetColumns(rows);
  if (!detected) {
    throw new Error('Unable to locate Register Number, Student Name, and final TOTAL columns.');
  }
  const totals = new Map<string, CdpMarkEntryParsedStudentValue>();
  for (let rowIndex = detected.header_row_index + 1; rowIndex < rows.length; rowIndex += 1) {
    const row = rows[rowIndex];
    if (!Array.isArray(row)) continue;
    const regNo = normalizeRegNo(row[detected.reg_col]);
    const studentName = String(row[detected.name_col] ?? '').trim();
    if (!regNo || !studentName) continue;
    const totalValue = row[detected.total_col];
    const hasValue = totalValue != null && String(totalValue).trim() !== '';
    const numericValue = hasValue && typeof totalValue === 'number'
      ? totalValue
      : (hasValue ? Number(String(totalValue).trim()) : NaN);
    totals.set(regNo, {
      has_value: hasValue,
      is_zero: hasValue && Number.isFinite(numericValue) && numericValue === 0,
    });
  }
  if (!totals.size) {
    throw new Error('No student rows were detected in the exam tab.');
  }
  return totals;
}

function buildCdpMarkEntrySnapshot(
  subject: NonNullable<ReturnType<typeof getSubjectById>>,
  workbook: XLSX.WorkBook,
  classRosters: CdpAttendanceRoster[],
  facultyAllocations: Array<{ faculty_name: string; class_sections: string[] }>,
): CdpMarkEntrySnapshot {
  const evaluateRosterMarkEntryCell = (
    roster: CdpAttendanceRoster | null,
    parsedTest: {
      status: 'available' | 'not_available' | 'error';
      message: string;
      totals: Map<string, CdpMarkEntryParsedStudentValue>;
    },
  ) => {
    if (parsedTest.status === 'not_available') {
      return createCdpMarkEntryCell('not_available', 0, 0, parsedTest.message);
    }
    if (parsedTest.status === 'error') {
      return createCdpMarkEntryCell('error', 0, 0, parsedTest.message);
    }
    if (!roster || !roster.student_reg_nos.length) {
      return createCdpMarkEntryCell('error', 0, 0, 'Class roster unavailable from Daily Attendance sheet.');
    }

    const values = roster.student_reg_nos
      .map((regNo) => parsedTest.totals.get(regNo) || { has_value: false, is_zero: false });
    const filledStudents = values.filter((value) => value.has_value).length;
    const zeroStudents = values.filter((value) => value.is_zero).length;
    const zeroRatio = roster.student_reg_nos.length ? zeroStudents / roster.student_reg_nos.length : 0;
    const suspiciousZeroPattern = zeroStudents > 0 && zeroRatio >= CDP_MARK_ENTRY_ZERO_PATTERN_THRESHOLD;

    if (suspiciousZeroPattern) {
      return createCdpMarkEntryCell(
        'pending',
        0,
        roster.student_reg_nos.length,
        zeroStudents === roster.student_reg_nos.length
          ? 'All TOTAL values are 0 for this class, so this test is treated as incomplete.'
          : `Most TOTAL values are 0 for this class (${zeroStudents}/${roster.student_reg_nos.length}), so this test is treated as incomplete.`,
      );
    }

    return createCdpMarkEntryCell(
      filledStudents === roster.student_reg_nos.length ? 'complete' : 'pending',
      filledStudents,
      roster.student_reg_nos.length,
    );
  };

  const rosterMap = new Map(
    classRosters.map((roster) => [roster.normalized_label, roster] as const),
  );
  const parsedTests = new Map<CdpMarkEntryTestKey, {
    status: 'available' | 'not_available' | 'error';
    message: string;
    totals: Map<string, CdpMarkEntryParsedStudentValue>;
  }>();

  for (const test of CDP_MARK_ENTRY_TESTS) {
    const sheetName = findCdpMarkEntrySheetName(workbook, test.aliases);
    if (!sheetName) {
      parsedTests.set(test.key, {
        status: 'not_available',
        message: `${test.label} tab is not available in this workbook.`,
        totals: new Map<string, CdpMarkEntryParsedStudentValue>(),
      });
      continue;
    }
    try {
      parsedTests.set(test.key, {
        status: 'available',
        message: '',
        totals: parseCdpMarkEntrySheetData(workbook, sheetName),
      });
    } catch (error) {
      parsedTests.set(test.key, {
        status: 'error',
        message: error instanceof Error ? error.message : 'Unable to parse this exam tab.',
        totals: new Map<string, CdpMarkEntryParsedStudentValue>(),
      });
    }
  }

  const rowDefinitions = Array.from(new Set(
    facultyAllocations.flatMap((entry) => {
      const facultyName = String(entry.faculty_name || '').trim();
      const classes = Array.from(new Set(
        (entry.class_sections || [])
          .map((value) => normalizeParsedClassLabel(String(value || '').trim(), subject.department))
          .filter(Boolean),
      ));
      return classes.map((classLabel) => `${facultyName}::${classLabel}`);
    }),
  ))
    .map((value) => {
      const [facultyName, classLabel] = value.split('::');
      return {
        faculty_name: facultyName,
        class_label: classLabel,
      };
    })
    .filter((entry) => entry.faculty_name && entry.class_label);

  const rows: CdpMarkEntryRow[] = rowDefinitions.map((entry) => {
    const roster = rosterMap.get(entry.class_label) || null;
    const tests = Object.fromEntries(
      CDP_MARK_ENTRY_TESTS.map((test) => {
        const parsedTest = parsedTests.get(test.key)!;
        const cell = evaluateRosterMarkEntryCell(roster, parsedTest);
        return [test.key, cell];
      }),
    ) as Record<CdpMarkEntryTestKey, CdpMarkEntryCell>;
    return {
      faculty_name: entry.faculty_name,
      class_label: entry.class_label,
      tests,
    };
  });

  const uniqueAllocatedClasses = Array.from(new Set(rowDefinitions.map((entry) => entry.class_label)));
  const summaries: CdpMarkEntrySummary[] = CDP_MARK_ENTRY_TESTS.map((test) => {
    const parsedTest = parsedTests.get(test.key)!;
    const classCells = uniqueAllocatedClasses.map((classLabel) =>
      evaluateRosterMarkEntryCell(rosterMap.get(classLabel) || null, parsedTest),
    );
    const status =
      classCells.some((cell) => cell.status === 'error')
        ? 'error'
        : (classCells.some((cell) => cell.status === 'pending')
          ? 'pending'
          : (classCells.some((cell) => cell.status === 'complete') ? 'complete' : 'not_available'));
    const totalStudents = classCells.reduce((sum, cell) => sum + Number(cell.total_students || 0), 0);
    const filledStudents = classCells.reduce((sum, cell) => sum + Number(cell.filled_students || 0), 0);
    const summaryMessage =
      classCells.find((cell) => cell.status === 'error' && cell.message)?.message
      || classCells.find((cell) => cell.status === 'pending' && cell.message)?.message
      || (parsedTest.status !== 'available' ? parsedTest.message : '');
    return {
      key: test.key,
      label: test.label,
      ...createCdpMarkEntryCell(status, filledStudents, totalStudents, summaryMessage),
    };
  });

  return { summaries, rows };
}

async function parseCdpSheetStatus(subject: ReturnType<typeof getSubjectById>) {
  if (!subject) throw new Error('Subject not found.');

  const cached = cdpStatusCache.get(subject.id);
  if (cached && Date.now() - cached.timestamp < CDP_STATUS_CACHE_TTL_MS) {
    return cached.data;
  }

  const sheetUrl = String(subject.google_sheet_link || '').trim();
  if (!sheetUrl) {
    throw new Error('Google Sheet link is missing for this subject.');
  }

  const match = sheetUrl.match(/\/d\/([a-zA-Z0-9-_]+)/);
  if (!match) {
    throw new Error('Invalid Google Sheet URL.');
  }

  const exportUrl = `https://docs.google.com/spreadsheets/d/${match[1]}/export?format=xlsx`;
  const response = await fetch(exportUrl, {
    headers: { 'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64)' },
  });
  if (!response.ok) {
    throw new Error('Sheet download failed. Ensure the sheet is shared as "Anyone with link can view".');
  }

  const workbookBuffer = Buffer.from(await response.arrayBuffer());
  const workbook = XLSX.read(workbookBuffer, { type: 'buffer', cellStyles: true });
  let sheetName = workbook.SheetNames.find((name) => name.toLowerCase().replace(/_/g, ' ').includes('daily attendance'));
  if (!sheetName) sheetName = workbook.SheetNames.find((name) => name.toLowerCase().includes('attendance'));
  if (!sheetName) sheetName = workbook.SheetNames[0];
  if (!sheetName) {
    throw new Error('The workbook contains no readable attendance sheet.');
  }

  const sheet = workbook.Sheets[sheetName];
  const unavailableStudentRows = await extractUnavailableStudentRowsFromWorkbook(workbookBuffer, sheetName);
  const rows = XLSX.utils.sheet_to_json<unknown[]>(sheet, { header: 1, defval: null, raw: true });
  const todayLabel = getTodaySheetLabel();
  const classes: CdpClassStatus[] = [];
  const classRosters: CdpAttendanceRoster[] = [];
  const letters = ['A', 'B', 'C', 'D', 'E', 'F'];
  const allocatedClasses = new Set(
    (subject.class_sections || [])
      .map((value) => normalizeParsedClassLabel(String(value || '').trim(), subject.department))
      .filter(Boolean),
  );

  const boundaryRows: number[] = [];
  for (let rowIndex = 0; rowIndex < rows.length; rowIndex += 1) {
    const row = rows[rowIndex];
    if (!Array.isArray(row)) continue;
    const text = row.map((cell) => String(cell ?? '')).join(' ').toLowerCase();
    if (
      text.includes('rmkcet')
      || text.includes('r.m.k.c.e.t')
      || text.includes('rmk')
      || text.includes('college of engineering')
    ) {
      const last = boundaryRows[boundaryRows.length - 1];
      if (last === undefined || rowIndex - last > 3) boundaryRows.push(rowIndex);
    }
  }

  const sections = (boundaryRows.length ? boundaryRows : [0]).map((startRow, index, source) => ({
    startRow,
    endRow: source[index + 1] !== undefined ? source[index + 1] - 1 : rows.length - 1,
    label: letters[index] || `Section ${index + 1}`,
  }));

  for (const section of sections) {
    const sectionRows = rows.slice(section.startRow, section.endRow + 1);
    let dateRowIndex = -1;
    let dateColumns: Array<{ colIndex: number; label: string; dateObj: Date; periodLabel: string }> = [];

    for (let localRowIndex = 0; localRowIndex < sectionRows.length; localRowIndex += 1) {
      const row = sectionRows[localRowIndex];
      if (!Array.isArray(row)) continue;
      if (isAttendanceStudentRow(row)) break;
      const found: Array<{ colIndex: number; label: string; dateObj: Date; periodLabel: string }> = [];
      let started = false;

      for (let colIndex = 0; colIndex < row.length; colIndex += 1) {
        const cellKey = XLSX.utils.encode_cell({ r: section.startRow + localRowIndex, c: colIndex });
        const cell = sheet[cellKey];
        const rawValue = String(cell?.w ?? row[colIndex] ?? '').trim();
        const dateObj = parseSheetDateToken(row[colIndex], subject, cell);
        if (!dateObj) {
          if (started && !rawValue) break;
          continue;
        }
        started = true;
        const periodRow = sectionRows[localRowIndex + 1];
        const periodLabel = Array.isArray(periodRow) ? String(periodRow[colIndex] ?? '').trim() : '';
        found.push({
          colIndex,
          label: `${String(dateObj.getDate()).padStart(2, '0')}/${String(dateObj.getMonth() + 1).padStart(2, '0')}`,
          dateObj,
          periodLabel,
        });
      }
      const contiguousFound = keepLeadingContiguousDateColumns(found);

      if (contiguousFound.length >= 3 && looksLikeAttendanceDateHeader(row, sectionRows[localRowIndex + 1]) && contiguousFound.length > dateColumns.length) {
        dateColumns = contiguousFound;
        dateRowIndex = localRowIndex;
      }
    }

    if (!dateColumns.length) continue;

    const today = new Date();
    const todayMidnight = new Date(today.getFullYear(), today.getMonth(), today.getDate());
    const validDateColumns = dateColumns.filter((item) => {
      const candidate = new Date(item.dateObj.getFullYear(), item.dateObj.getMonth(), item.dateObj.getDate());
      return candidate <= todayMidnight;
    });
    if (!validDateColumns.length) continue;

    let classLabel = normalizeParsedClassLabel(section.label, subject.department);
    if (dateRowIndex > 0) {
      const rawLabel = String(sectionRows[dateRowIndex - 1]?.[2] ?? '').trim();
      if (rawLabel && isDepartmentClassLabel(rawLabel, subject.department)) {
        classLabel = normalizeParsedClassLabel(rawLabel, subject.department);
      }
    }
    const normalizedClassLabel = normalizeParsedClassLabel(classLabel, subject.department);
    if (allocatedClasses.size && !allocatedClasses.has(normalizedClassLabel)) {
      continue;
    }

    const allSectionStudentRows = sectionRows.flatMap((row, localRowIndex) => {
      if (!Array.isArray(row) || !isAttendanceStudentRow(row)) return [];
      return [row];
    });
    const filteredStudentRows = sectionRows.flatMap((row, localRowIndex) => {
      if (!Array.isArray(row) || !isAttendanceStudentRow(row)) return [];
      const worksheetRowNumber = section.startRow + localRowIndex + 1;
      if (unavailableStudentRows.has(worksheetRowNumber)) return [];
      return [row];
    });
    const studentRows =
      filteredStudentRows.length || !allSectionStudentRows.length
        ? filteredStudentRows
        : allSectionStudentRows;
    const studentRegNos = Array.from(new Set(
      studentRows
        .map((row) => normalizeRegNo(String(row[1] ?? '')))
        .filter(Boolean),
    ));

    let completedDates = 0;
    let totalDates = 0;
    let todayColExists = false;
    let todayColFilled = false;
    const pendingDates = new Set<string>();
    let missingEntryCount = 0;

    for (const column of validDateColumns) {
      const normalizedLabel = normalizeSheetDateLabel(column.label);
      if (normalizedLabel === todayLabel) todayColExists = true;

      const filledStudentCount = studentRows.filter((row) => {
        const value = row[column.colIndex];
        return value != null && String(value).trim() !== '';
      }).length;

      totalDates += 1;
      const filled = studentRows.length > 0 && filledStudentCount === studentRows.length;
      if (filled) {
        completedDates += 1;
        if (normalizedLabel === todayLabel) todayColFilled = true;
      } else if (normalizedLabel) {
        missingEntryCount += Math.max(0, studentRows.length - filledStudentCount);
        pendingDates.add(normalizedLabel);
      }
    }

    classes.push({
      label: classLabel,
      total_date_cols: totalDates,
      filled_cols: completedDates,
      completion_pct: totalDates ? Math.round((completedDates / totalDates) * 100) : 100,
      today_col_exists: todayColExists,
      today_col_filled: todayColFilled,
      pending_dates: Array.from(pendingDates).sort((a, b) => a.localeCompare(b)),
      missing_entry_count: missingEntryCount,
    });
    classRosters.push({
      label: classLabel,
      normalized_label: normalizedClassLabel,
      student_reg_nos: studentRegNos,
    });
  }

  const overallTotal = classes.reduce((sum, item) => sum + item.total_date_cols, 0);
  const overallFilled = classes.reduce((sum, item) => sum + item.filled_cols, 0);
  const classStatusMap = new Map(
    classes.map((item) => [normalizeParsedClassLabel(String(item.label || '').trim(), subject.department), item]),
  );
  const facultyAllocations = (subject.faculty_allocations || []).length
    ? subject.faculty_allocations
    : splitFacultyNames(subject.faculty_name || '').map((facultyName) => ({
      faculty_name: facultyName,
      class_sections: subject.class_sections || [],
    }));
  const facultyStatuses: CdpFacultyStatus[] = facultyAllocations.map((entry) => {
    const classSections = Array.from(new Set(
      (entry.class_sections || [])
        .map((value) => normalizeParsedClassLabel(String(value || '').trim(), subject.department))
        .filter(Boolean),
    ));
    const pendingClasses: string[] = [];
    const pendingDates = new Set<string>();
    const notes: string[] = [];
    let missingEntryCount = 0;
    let filledCols = 0;
    let totalDateCols = 0;
    const classBreakdown: CdpFacultyStatus['class_breakdown'] = [];

    for (const classSection of classSections) {
      const classStatus = classStatusMap.get(classSection) || null;
      if (!classStatus) {
        pendingClasses.push(classSection);
        notes.push(`${classSection} was allocated but not detected in the Daily Attendance sheet.`);
        classBreakdown.push({
          class_label: classSection,
          filled_cols: 0,
          total_date_cols: 0,
          completion_pct: 0,
          pending_dates: [],
          missing_entry_count: 0,
        });
        continue;
      }
      filledCols += Number(classStatus.filled_cols || 0);
      totalDateCols += Number(classStatus.total_date_cols || 0);
      classBreakdown.push({
        class_label: classSection,
        filled_cols: Number(classStatus.filled_cols || 0),
        total_date_cols: Number(classStatus.total_date_cols || 0),
        completion_pct: Number(classStatus.completion_pct || 0),
        pending_dates: classStatus.pending_dates || [],
        missing_entry_count: Number(classStatus.missing_entry_count || 0),
      });
      if (classStatus.pending_dates.length) {
        pendingClasses.push(classSection);
        classStatus.pending_dates.forEach((value) => pendingDates.add(value));
      }
      missingEntryCount += Number(classStatus.missing_entry_count || 0);
    }

    return {
      faculty_name: entry.faculty_name,
      class_sections: classSections,
      status: pendingClasses.length ? 'pending' : 'ready',
      filled_cols: filledCols,
      total_date_cols: totalDateCols,
      completion_pct: totalDateCols ? Math.round((filledCols / totalDateCols) * 100) : 100,
      pending_class_count: pendingClasses.length,
      pending_dates: Array.from(pendingDates).sort((a, b) => a.localeCompare(b)),
      pending_classes: pendingClasses,
      missing_entry_count: missingEntryCount,
      class_breakdown: classBreakdown,
      notes,
    } satisfies CdpFacultyStatus;
  });
  const pendingFacultyCount = facultyStatuses.filter((entry) => entry.status === 'pending').length;
  const pendingClassCount = Array.from(new Set(facultyStatuses.flatMap((entry) => entry.pending_classes))).length;
  const pendingDateCount = Array.from(new Set(classes.flatMap((item) => item.pending_dates))).length;
  const markEntry = buildCdpMarkEntrySnapshot(subject, workbook, classRosters, facultyAllocations);
  const payload: CdpSubjectStatus = {
    subject_id: subject.id,
    subject_code: subject.subject_code,
    subject_name: subject.subject_name,
    faculty_name: subject.faculty_name,
    department: subject.department,
    year_level: subject.year_level,
    semester: subject.semester,
    classes,
    faculty_statuses: facultyStatuses,
    overall_filled_cols: overallFilled,
    overall_total_cols: overallTotal,
    overall_completion_pct: overallTotal ? Math.round((overallFilled / overallTotal) * 100) : 100,
    today_pending: classes.some((item) => item.today_col_exists && !item.today_col_filled),
    summary_status: pendingFacultyCount ? 'pending' : 'ready',
    faculty_count: facultyStatuses.length,
    allocated_class_count: Array.from(new Set(facultyStatuses.flatMap((entry) => entry.class_sections))).length,
    pending_faculty_count: pendingFacultyCount,
    pending_class_count: pendingClassCount,
    pending_date_count: pendingDateCount,
    parsed_at: new Date().toISOString(),
    mark_entry: markEntry,
  };

  cdpStatusCache.set(subject.id, { timestamp: Date.now(), data: payload });
  return payload;
}

function persistCdpSnapshotFromStatus(subject: NonNullable<ReturnType<typeof getSubjectById>>, status: CdpSubjectStatus) {
  return upsertCdpSubjectSnapshot({
    subject_id: subject.id,
    department: subject.department,
    year_level: subject.year_level,
    semester: subject.semester,
    summary_status: status.summary_status,
    faculty_count: status.faculty_count,
    allocated_class_count: status.allocated_class_count,
    pending_faculty_count: status.pending_faculty_count,
    pending_class_count: status.pending_class_count,
    pending_date_count: status.pending_date_count,
    parsed_at: status.parsed_at,
    parser_error: '',
    class_statuses: status.classes,
    faculty_statuses: status.faculty_statuses,
    mark_entry_statuses: status.mark_entry,
  });
}

function persistCdpSnapshotError(subject: NonNullable<ReturnType<typeof getSubjectById>>, errorMessage: string) {
  const normalizedError = String(errorMessage || 'Unable to parse the selected Google Sheet.').trim();
  return upsertCdpSubjectSnapshot({
    subject_id: subject.id,
    department: subject.department,
    year_level: subject.year_level,
    semester: subject.semester,
    summary_status: 'error',
    faculty_count: subject.faculty_allocations.length || splitFacultyNames(subject.faculty_name || '').length,
    allocated_class_count: subject.class_sections.length,
    pending_faculty_count: 0,
    pending_class_count: 0,
    pending_date_count: 0,
    parsed_at: new Date().toISOString(),
    parser_error: normalizedError,
    class_statuses: [],
    faculty_statuses: [],
    mark_entry_statuses: buildCdpMarkEntryErrorSnapshot(normalizedError),
  });
}

async function rebuildCdpScopeOverviewPayload(
  authUser: ReturnType<typeof toAuthUser>,
  options: {
    requestedDepartment: string;
    requestedYear: number | null;
    requestedSemester: string;
    requestedSubjectId: number | null;
  },
) {
  const departments = getVisibleDepartmentsForActor(authUser);
  const yearsByDepartment = getScopedYearsByDepartment(authUser);
  const visibleSubjects = listSubjectsForActor(authUser);
  const availableSemesters = ['1', '2'];
  const selectedDepartment =
    options.requestedDepartment && departments.some((department) => department.code.toUpperCase() === options.requestedDepartment)
      ? options.requestedDepartment
      : (departments.length === 1 ? departments[0].code.toUpperCase() : '');
  const availableYears = selectedDepartment
    ? Array.from(new Set(yearsByDepartment.get(selectedDepartment) || [])).sort((a, b) => a - b)
    : [];
  const selectedYear =
    options.requestedYear && availableYears.includes(options.requestedYear)
      ? options.requestedYear
      : (availableYears.length === 1 ? availableYears[0] : null);
  const selectedSemester = availableSemesters.includes(options.requestedSemester)
    ? options.requestedSemester
    : '';
  if (!selectedDepartment || !selectedYear || !selectedSemester) {
    return buildCdpOverviewPayload(authUser, options);
  }

  const scopedSubjects = visibleSubjects.filter((subject) =>
    subject.department === selectedDepartment && subject.year_level === selectedYear && subject.semester === selectedSemester,
  );
  await Promise.all(scopedSubjects.map(async (subject) => {
    clearCdpStatusCache(subject.id);
    try {
      const status = await parseCdpSheetStatus(subject);
      persistCdpSnapshotFromStatus(subject, status);
    } catch (error) {
      persistCdpSnapshotError(subject, error instanceof Error ? error.message : 'Unable to parse the selected Google Sheet.');
    }
  }));
  bumpReadModelCacheVersion();
  return buildCdpOverviewPayload(authUser, options);
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
  const oauthAttempts = getOauthAttemptStatistics();
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
      today_unregistered_attempts: oauthAttempts.today_unregistered_attempts,
      total_unregistered_attempts: oauthAttempts.total_unregistered_attempts,
      latest_unregistered_attempt_email: oauthAttempts.latest_unregistered_attempt_email,
      latest_unregistered_attempt_name: oauthAttempts.latest_unregistered_attempt_name,
      latest_unregistered_attempt_time: oauthAttempts.latest_unregistered_attempt_time,
      latest_unregistered_attempt_reason: oauthAttempts.latest_unregistered_attempt_reason,
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
  const toPercentInt = (completed: number, total: number) => {
    const safeCompleted = Math.max(0, Number(completed || 0));
    const safeTotal = Math.max(0, Number(total || 0));
    if (safeTotal <= 0) return 0;
    if (safeCompleted >= safeTotal) return 100;
    return Math.max(0, Math.floor((safeCompleted / safeTotal) * 100));
  };

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
      return toPercentInt(bucket.completed, bucket.total);
    });
    const departmentYearBreakdown = Object.fromEntries(
      departmentLabels.map((department) => {
        const years = buckets.get(department)?.years || {};
        return [
          department,
          Object.fromEntries(
            Object.entries(years).map(([year, value]) => [
              Number(year),
              toPercentInt(value.completed, value.total),
            ]),
          ),
        ];
      }),
    );

    return {
      overall: toPercentInt(completedTotal, grandTotal),
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
    return withReadModelMeta({
      ...payload,
      admin_status: await getAdminDashboardStatus(),
    });
  }
  return withReadModelMeta(payload);
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
      const snapshot = getCounselorActivityScopeSnapshot(
        departmentCode,
        yearLevel,
        uploadedTests.map((test) => ({
          test_id: test.test_id,
          department: test.department,
          year_level: test.year_level,
          semester: test.semester,
          test_name: test.test_name,
        })),
      );

      for (const test of uploadedTests) {
        const semester = String(test.semester || '').trim();
        const testName = String(test.test_name || '').trim().toUpperCase();
        const result = snapshot.results.find((item) => item.semester === semester && item.test_name === testName)
          || getCounselorActivityForTest(departmentCode, yearLevel, semester, testName, '', 'pending_first');
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

function getAcademicYearLabelFromArchiveName(fileName: string) {
  const normalized = String(fileName || '').trim();
  const match = normalized.match(/archive[_-](\d{4})[_-](\d{4})(?:\.db)?$/i);
  if (match) {
    return `${match[1]}-${match[2]}`;
  }
  const compact = normalized.replace(/^archive[_-]?/i, '').replace(/\.db$/i, '');
  return compact.replace(/[_\s]+/g, '-');
}

function decorateArchiveRecord<T extends { name: string; size_kb: number; modified: string }>(record: T) {
  return {
    ...record,
    academic_year_label: getAcademicYearLabelFromArchiveName(record.name),
  };
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
    return (await listDriveArchiveFiles()).map((record) => decorateArchiveRecord(record));
  }
  return (await listLocalArchiveFiles()).map((record) => decorateArchiveRecord(record));
}

function getArchiveSnapshotDirFromName(fileName: string) {
  return `${fileName}${BACKUP_SNAPSHOT_SUFFIX}`;
}

async function archiveExistsLocally(fileName: string) {
  try {
    await stat(resolve(ARCHIVE_DIR, fileName));
    return true;
  } catch {
    return false;
  }
}

async function ensureLocalArchiveFile(fileName: string) {
  await mkdir(ARCHIVE_DIR, { recursive: true });
  const localPath = resolve(ARCHIVE_DIR, fileName);
  if (await archiveExistsLocally(fileName)) {
    return localPath;
  }
  if (getBackupStorageMode() !== 'gdrive') {
    throw new Error('Archive file not found.');
  }
  const buffer = await downloadDriveFileFromPath(['archives'], fileName);
  await writeFile(localPath, buffer);
  return localPath;
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
    expires: sessionCookieExpires(appConfig),
  });

  return {
    success: true,
    user: toAuthUser(userRow),
  };
}

async function beginResolvedLogin(
  c: Context,
  userRow: Record<string, unknown>,
  options?: {
    forceLogoutOthers?: boolean;
    authMethod?: 'password' | 'google';
    skipOtp?: boolean;
  },
) {
  const forceLogoutOthers = Boolean(options?.forceLogoutOthers);
  const authMethod = options?.authMethod || 'password';
  const skipOtp = Boolean(options?.skipOtp);
  const userEmail = String(userRow.email || '').toLowerCase();
  if (getTestModeBlockForUser(userEmail)) {
    return {
      status: 423,
      payload: { error: 'This account is currently being reviewed in admin test mode. Please try again after the admin exits test mode.' },
    };
  }
  const access = checkUserAccess(userEmail);
  if (!access.allowed) {
    return {
      status: 403,
      payload: { error: access.message },
    };
  }

  const appConfig = getAppConfig();
  const allowConcurrent = String(appConfig.allow_concurrent_sessions || 'false').toLowerCase() === 'true';
  if (!allowConcurrent && !forceLogoutOthers) {
    const activeSession = getActiveSessionForUser(userEmail);
    if (activeSession) {
      return {
        status: 409,
        payload: {
          error: 'Active session detected.',
          requiresForceLogout: true,
          existingSession: activeSession,
        },
      };
    }
  }

  if (!skipOtp && authMethod === 'password' && isLoginOtpRequiredForUser(userRow, appConfig)) {
    if (getSmtpStatus().state !== 'ready') {
      return {
        status: 400,
        payload: { error: 'SMTP is not ready. Login OTP delivery is unavailable.' },
      };
    }
    const challenge = await createLoginOtpChallenge(c, userRow, forceLogoutOthers || !allowConcurrent);
    if (!challenge) {
      return {
        status: 400,
        payload: { error: 'Unable to send login OTP. Verify SMTP settings and try again.' },
      };
    }
    return {
      status: 200,
      payload: {
        success: true,
        requiresOtp: true,
        maskedEmail: challenge.maskedEmail,
      },
    };
  }

  return {
    status: 200,
    payload: finalizeLogin(c, userRow, forceLogoutOthers || !allowConcurrent, authMethod),
  };
}

app.use(
  '/api/*',
  cors({
    origin: (origin) => {
      const safeOrigin = String(origin || '').trim();
      if (!safeOrigin) return CLIENT_ORIGIN;
      if (CLIENT_ORIGINS.includes(safeOrigin)) return safeOrigin;
      return null;
    },
    allowHeaders: ['Content-Type'],
    allowMethods: ['GET', 'POST', 'OPTIONS'],
    credentials: true,
  }),
);

app.use('/api/*', async (c, next) => {
  const startedAt = Date.now();
  const requestPath = new URL(c.req.url).pathname;
  const sessionId = getCookie(c, SESSION_COOKIE) || '';
  const existingSessionNotice = readSessionEndNotice(c);
  if (existingSessionNotice) {
    c.set('sessionEndNotice', existingSessionNotice);
  }
  if (sessionId) {
    const previewEmail = String(getCookie(c, TEST_MODE_COOKIE) || '').trim().toLowerCase();
    if (previewEmail) {
      const sessionActivity = getSessionLastActivityInfo(sessionId);
      if (sessionActivity && isTimestampOlderThan(sessionActivity.last_activity, TEST_MODE_IDLE_TIMEOUT_MS)) {
        releaseTestModeBlockForAdminSession(sessionId);
        deleteCookie(c, TEST_MODE_COOKIE, { path: '/' });
      }
    }
    const user = validateSession(sessionId);
    if (user) {
      c.set('sessionAuthUser', user);
      c.set('sessionId', sessionId);
      const refreshedPreviewEmail = String(getCookie(c, TEST_MODE_COOKIE) || '').trim().toLowerCase();
      if (user.role === 'admin' && refreshedPreviewEmail) {
        const previewUserRow = getUserByEmail(refreshedPreviewEmail);
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
    } else {
      const notice = buildSessionEndNotice(getLogoutReasonForSession(sessionId));
      if (notice) {
        setSessionEndNoticeCookie(c, notice);
        c.set('sessionEndNotice', notice);
      }
      deleteCookie(c, SESSION_COOKIE, { path: '/' });
      deleteCookie(c, TEST_MODE_COOKIE, { path: '/' });
      releaseTestModeBlockForAdminSession(String(sessionId));
    }
  }
  const authUser = c.get('authUser') || null;
  const archiveCookieName = String(getCookie(c, ARCHIVE_VIEW_COOKIE) || '').trim();
  const isArchivePreviewAllowedUser = Boolean(authUser && (isSystemAdmin(authUser.role) || isPrincipal(authUser.role)));
  let requestHandled = false;
  let archiveDb: ReturnType<typeof openReadOnlyDatabase> | null = null;
  let temporaryArchivePath = '';

  try {
    if (archiveCookieName && isArchivePreviewAllowedUser) {
      const archiveNames = new Set((await listArchiveFiles()).map((record) => String(record.name || '').trim()));
      if (!archiveNames.has(archiveCookieName)) {
        clearArchiveViewCookie(c);
      } else {
        const allowedReadOnlyPosts = new Set([
          '/api/session/heartbeat',
          '/api/auth/logout',
          '/api/database/archive-view/exit',
        ]);
        if (!['GET', 'HEAD', 'OPTIONS'].includes(c.req.method) && !allowedReadOnlyPosts.has(requestPath)) {
          return c.json({ error: 'Archive view is read-only. Exit archive view to make changes.' }, 403);
        }

        if (!(await archiveExistsLocally(archiveCookieName)) && getBackupStorageMode() === 'gdrive') {
          const tempRoot = await mkdtemp(resolve(tmpdir(), 'shine-archive-preview-'));
          temporaryArchivePath = resolve(tempRoot, archiveCookieName);
          const archiveBuffer = await downloadDriveFileFromPath(['archives'], archiveCookieName);
          await writeFile(temporaryArchivePath, archiveBuffer);
          archiveDb = openReadOnlyDatabase(temporaryArchivePath);
        } else {
          archiveDb = openReadOnlyDatabase(await ensureLocalArchiveFile(archiveCookieName));
        }

        c.set('archiveView', buildArchiveViewState(archiveCookieName));
        await withDatabaseContext(archiveDb, async () => {
          requestHandled = true;
          await next();
        });
      }
    }

    if (!requestHandled) {
      await next();
    }
  } finally {
    if (archiveDb) {
      try {
        archiveDb.close();
      } catch {
        // Ignore archive preview cleanup failures.
      }
    }
    if (temporaryArchivePath) {
      await rm(dirname(temporaryArchivePath), { recursive: true, force: true }).catch(() => undefined);
    }
    appendServerConsoleLine(`${c.req.method} ${requestPath} -> ${c.res.status} (${Date.now() - startedAt} ms)`);
  }
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
    <script>${FOOTER_THEME_BOOT_SCRIPT}</script>
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

type DesktopInstallerManifest = {
  schemaVersion: number;
  channel: string;
  appName: string;
  version: string;
  packageVersion?: string;
  packageType?: string;
  preferredInstaller?: string;
  packageName?: string;
  publisher: string;
  architecture: string;
  publishedAt: string;
  releaseNotes: string[];
  files: {
    msix?: {
      fileName: string;
      relativePath: string;
    };
    appinstaller?: {
      fileName: string;
      relativePath: string;
    };
    exe?: {
      fileName: string;
      relativePath: string;
      versionedRelativePath?: string;
    };
  };
};

const DESKTOP_INSTALLER_LATEST_MANIFEST_PATH = resolve(DESKTOP_INSTALLER_ROOT, 'latest', 'release.json');

async function readDesktopInstallerManifest(): Promise<DesktopInstallerManifest | null> {
  try {
    const raw = JSON.parse(await readFile(DESKTOP_INSTALLER_LATEST_MANIFEST_PATH, 'utf8')) as DesktopInstallerManifest;
    const hasMsixChannel = !!raw?.files?.appinstaller?.relativePath && !!raw?.files?.msix?.relativePath;
    const hasExeChannel = !!raw?.files?.exe?.relativePath;
    if (!hasMsixChannel && !hasExeChannel) return null;
    return raw;
  } catch {
    return null;
  }
}

function resolveDesktopInstallerArtifactPath(relativePath: string) {
  const normalized = String(relativePath || '')
    .trim()
    .replace(/^\/+/, '')
    .replace(/\\/g, '/');
  if (!normalized) return null;
  const resolvedPath = resolve(DESKTOP_INSTALLER_ROOT, normalized);
  const isInsideRoot =
    resolvedPath === DESKTOP_INSTALLER_ROOT ||
    resolvedPath.startsWith(`${DESKTOP_INSTALLER_ROOT}/`) ||
    resolvedPath.startsWith(`${DESKTOP_INSTALLER_ROOT}\\`);
  return isInsideRoot ? resolvedPath : null;
}

app.get('/api/desktop/installer/meta', async (c) => {
  const manifest = await readDesktopInstallerManifest();
  if (!manifest) {
    return c.json({ available: false, error: 'Desktop installer has not been published yet.' }, 404);
  }

  const requestOrigin = getPublicRequestOrigin(c);
  const appinstallerUrl = manifest.files.appinstaller?.relativePath ? `${requestOrigin}${manifest.files.appinstaller.relativePath}` : '';
  const msixUrl = manifest.files.msix?.relativePath ? `${requestOrigin}${manifest.files.msix.relativePath}` : '';
  const exeUrl = manifest.files.exe?.relativePath ? `${requestOrigin}${manifest.files.exe.relativePath}` : '';
  return c.json({
    available: true,
    ...manifest,
    installUrl: appinstallerUrl ? `ms-appinstaller:?source=${encodeURIComponent(appinstallerUrl)}` : '',
    appinstallerUrl,
    msixUrl,
    exeUrl,
  });
});

app.get('/api/desktop/installer', async (c) => {
  const manifest = await readDesktopInstallerManifest();
  const requestOrigin = getPublicRequestOrigin(c);
  const appinstallerUrl = manifest?.files.appinstaller?.relativePath ? `${requestOrigin}${manifest.files.appinstaller.relativePath}` : '';
  const msixUrl = manifest?.files.msix?.relativePath ? `${requestOrigin}${manifest.files.msix.relativePath}` : '';
  const exeUrl = manifest?.files.exe?.relativePath ? `${requestOrigin}${manifest.files.exe.relativePath}` : '';
  const installUrl = appinstallerUrl ? `ms-appinstaller:?source=${encodeURIComponent(appinstallerUrl)}` : '';
  const preferredInstaller = String(manifest?.preferredInstaller || '').trim().toLowerCase();
  const prefersExe = preferredInstaller === 'exe' || (!!exeUrl && !appinstallerUrl);
  const releaseNotesHtml = manifest?.releaseNotes?.length
    ? manifest.releaseNotes.map((item) => `<li>${escapeHtml(item)}</li>`).join('')
    : '<li>Latest Windows desktop installer channel is ready.</li>';

  return c.html(`<!DOCTYPE html>
<html lang="en">
  <head>
    <meta charset="utf-8" />
    <meta name="viewport" content="width=device-width, initial-scale=1" />
    <script>${FOOTER_THEME_BOOT_SCRIPT}</script>
    <title>Windows App - ${APP_NAME}</title>
    <style>${FOOTER_CREDITS_INLINE_CSS}
      .desktop-install-grid{display:grid;grid-template-columns:minmax(0,1.2fr) minmax(280px,.8fr);gap:22px}
      .desktop-install-card{background:var(--surface,rgba(255,255,255,.92));border:1px solid var(--border,rgba(148,163,184,.28));border-radius:24px;padding:24px;box-shadow:0 20px 50px rgba(15,23,42,.12)}
      .desktop-install-card.primary{position:relative;overflow:hidden}
      .desktop-install-card.primary:before{content:"";position:absolute;inset:0 0 auto 0;height:5px;background:linear-gradient(90deg,#667eea,#764ba2)}
      .desktop-install-actions{display:flex;flex-wrap:wrap;gap:12px;margin-top:20px}
      .desktop-install-btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;padding:12px 18px;border-radius:14px;border:1px solid rgba(99,102,241,.28);font-weight:800;text-decoration:none;background:linear-gradient(135deg,#667eea,#764ba2);color:#fff;box-shadow:0 12px 26px rgba(102,126,234,.24)}
      .desktop-install-btn.secondary{background:transparent;color:var(--text-main,#1e293b);border-color:var(--border,rgba(148,163,184,.28));box-shadow:none}
      .desktop-install-meta{display:grid;grid-template-columns:repeat(auto-fit,minmax(170px,1fr));gap:12px;margin-top:20px}
      .desktop-install-meta-item{padding:12px;border-radius:16px;background:rgba(99,102,241,.075);border:1px solid rgba(99,102,241,.12)}
      .desktop-install-meta-item strong{display:block;margin-bottom:4px;color:var(--text-main,#0f172a)}
      .desktop-install-pill{display:inline-flex;align-items:center;gap:8px;padding:7px 11px;border-radius:999px;background:rgba(99,102,241,.12);color:#4f46e5;font-size:.82rem;font-weight:800}
      .desktop-install-list{margin:14px 0 0;padding-left:18px;color:var(--text-dim,#475569);line-height:1.7}
      .desktop-install-note{margin-top:14px;font-size:.92rem;color:var(--text-dim,#475569);line-height:1.6}
      .desktop-install-warning{margin-top:16px;padding:14px 16px;border-radius:16px;background:rgba(245,158,11,.12);border:1px solid rgba(245,158,11,.28);color:#92400e;line-height:1.55}
      .desktop-install-empty{padding:16px 18px;border-radius:16px;background:rgba(59,130,246,.08);border:1px solid rgba(59,130,246,.18);color:var(--text-dim,#475569)}
      .desktop-install-heading{margin:16px 0 6px;font-size:1.25rem}
      @media (max-width: 860px){.desktop-install-grid{grid-template-columns:1fr}.desktop-install-btn{width:100%}}
    </style>
  </head>
  <body>
    <section class="credits-page">
      <div class="credits-page-hero">
        <div>
          <p class="credits-page-kicker">Desktop</p>
          <h1 class="credits-page-title">Install RMKCET Shine for Windows</h1>
          <p class="credits-page-subtitle">Download the Windows desktop build directly from the Shine server and install it on internal college PCs.</p>
        </div>
        <button class="credits-back-btn" type="button" onclick="if (window.history.length > 1) { window.history.back(); } else { window.location.href = '/'; }">Back</button>
      </div>
      <div class="credits-page-body">
        <div class="desktop-install-grid">
          <article class="desktop-install-card primary">
            ${manifest ? `
              <span class="desktop-install-pill">Version ${escapeHtml(manifest.version)}</span>
              <h2 class="desktop-install-heading">Windows desktop installer</h2>
              <p class="desktop-install-note">Use this installer for the Shine desktop client. The bottom ribbon Windows App link points to this same live release channel.</p>
              <div class="desktop-install-meta">
                <div class="desktop-install-meta-item"><strong>Package</strong>${escapeHtml(manifest.appName || manifest.packageName || 'RMKCET Shine')}</div>
                <div class="desktop-install-meta-item"><strong>Publisher</strong>${escapeHtml(manifest.publisher || 'RMKCET Shine')}</div>
                <div class="desktop-install-meta-item"><strong>Architecture</strong>${escapeHtml(manifest.architecture || 'x64')}</div>
                <div class="desktop-install-meta-item"><strong>Published</strong>${new Date(manifest.publishedAt).toLocaleString('en-GB')}</div>
              </div>
              <div class="desktop-install-actions">
                ${prefersExe && exeUrl ? `<a class="desktop-install-btn" href="${exeUrl}">Download Windows Installer (.exe)</a>` : ''}
                ${!prefersExe && installUrl ? `<a class="desktop-install-btn" href="${installUrl}">Install with App Installer</a>` : ''}
                ${!prefersExe && exeUrl ? `<a class="desktop-install-btn secondary" href="${exeUrl}">Download .exe Installer</a>` : ''}
                ${appinstallerUrl ? `<a class="desktop-install-btn secondary" href="${appinstallerUrl}">Download .appinstaller</a>` : ''}
                ${msixUrl ? `<a class="desktop-install-btn secondary" href="${msixUrl}">Download .msix</a>` : ''}
              </div>
              <ul class="desktop-install-list">${releaseNotesHtml}</ul>
              <div class="desktop-install-warning">
                ${prefersExe
                  ? 'Windows may show a SmartScreen reputation warning for direct .exe installs. For internal college rollout, download only from this Shine server and use "More info -> Run anyway" when required.'
                  : 'Store-style zero-warning installs are only guaranteed through Microsoft Store. Signed web-distributed releases are still the correct path here, but very first installs can still show Windows reputation prompts until trust builds.'}
              </div>
            ` : `
              <div class="desktop-install-empty">The Windows installer channel has not been published yet. Run the production launcher once to generate the latest EXE package.</div>
            `}
          </article>
          <article class="desktop-install-card">
            <h2 class="template-card-title">How this install path works</h2>
            <p class="desktop-install-note">Shine serves a stable installer manifest from this server. The desktop app checks the same release channel for updates, and the web footer always opens the current installer page.</p>
            <ul class="desktop-install-list">
              <li>Direct EXE download from the active Shine domain.</li>
              <li>Same shared Shine codebase for web and desktop.</li>
              <li>Hosted installer artifacts stay on the trusted Shine domain.</li>
              <li>Desktop versioning stays aligned with the repo release version.</li>
            </ul>
          </article>
        </div>
      </div>
    </section>
  </body>
</html>`);
});

app.get('/api/desktop/download/latest/:fileName', async (c) => {
  return serveDesktopInstallerDownload(c, `latest/${String(c.req.param('fileName') || '').trim()}`);
});

app.get('/api/desktop/download/releases/:version/:fileName', async (c) => {
  return serveDesktopInstallerDownload(
    c,
    `releases/${String(c.req.param('version') || '').trim()}/${String(c.req.param('fileName') || '').trim()}`,
  );
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
    <script>${FOOTER_THEME_BOOT_SCRIPT}</script>
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
    case '.msix':
      return 'application/msix';
    case '.appinstaller':
      return 'application/appinstaller';
    case '.exe':
      return 'application/vnd.microsoft.portable-executable';
    default:
      return 'application/octet-stream';
  }
}

app.get('/api/bootstrap', async (c) => {
  const authUser = c.get('authUser') || null;
  const sessionAuthUser = c.get('sessionAuthUser') || authUser || null;
  const testModeTarget = c.get('testModeTarget') || null;
  const sessionEndNotice = c.get('sessionEndNotice') || null;
  const archiveView = c.get('archiveView') || null;
  const appConfig = getAppConfig();
  const safeAppConfig = sanitizeAppConfigForClient(appConfig, authUser);
  const authUi = getAuthUiConfig(authUser, appConfig);
  const now = new Date();
  const roleSwitchOptions = authUser && !testModeTarget && !archiveView
    ? getAvailableRoleSwitchOptionsForUser(sessionAuthUser || authUser)
    : [];
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
  const defaultTab = String(authUser ? defaultTabForRole(authUser.role) : 'reports');
  const shouldPrefetchDashboard = Boolean(authUser && ['admin', 'principal', 'hod'].includes(authUser.role));
  const shouldPrefetchActivity = Boolean(authUser && ['admin', 'principal', 'hod', 'deo'].includes(authUser.role));
  const prefetched = authUser && ['admin', 'principal', 'hod', 'deo'].includes(authUser.role)
    ? await (async () => {
        const [dashboard, reports, activity, cdp] = await Promise.all([
          shouldPrefetchDashboard
            ? getCachedReadModelPayload('dashboard-overview', authUser, 'default', () => buildDashboardOverview(authUser))
            : Promise.resolve(null),
          defaultTab === 'reports'
            ? getCachedReadModelPayload(
            'reports-overview',
            authUser,
            JSON.stringify({ department: '', year: 0 }),
            () => buildReportsOverviewPayload(authUser, '', null),
          )
            : Promise.resolve(null),
          shouldPrefetchActivity
            ? getCachedReadModelPayload(
            'activity-overview',
            authUser,
            JSON.stringify({ department: '', year: 0, semester: '', test_name: '', q: '', sort: 'pending_first' }),
            () => buildActivityOverviewPayload(authUser, { sortMode: 'pending_first' }),
          )
            : Promise.resolve(null),
          defaultTab === 'cdp'
            ? getCachedReadModelPayload(
            'cdp-overview',
            authUser,
            JSON.stringify({ department: '', year: 0, semester: '', subject_id: 0 }),
            () => buildCdpOverviewPayload(authUser, {
              requestedDepartment: '',
              requestedYear: null,
              requestedSemester: '',
              requestedSubjectId: null,
            }),
          )
            : Promise.resolve(null),
        ]);
        return { dashboard, reports, activity, cdp };
      })()
    : undefined;

  if (sessionEndNotice) {
    deleteCookie(c, SESSION_NOTICE_COOKIE, { path: '/' });
  }

  return c.json({
    appName: APP_NAME,
    appVersion: APP_VERSION,
    appConfig: safeAppConfig,
    authUi,
    nowLabel,
    user: authUser,
    roleSwitchOptions,
    sessionEndNotice,
    archiveView,
    testMode: {
      active: Boolean(testModeTarget),
      sessionUser: sessionAuthUser,
      targetUser: testModeTarget,
    },
    navTabs: authUser ? allowedTabsForRole(authUser.role) : [],
    defaultTab,
    metrics: getDashboardMetrics(authUser),
    readModelVersion: readModelCacheVersion,
    prefetched,
    counselorOverview,
    counselorTests,
  });
});

app.get('/api/dashboard/overview', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const payload = await getCachedReadModelPayload(
    'dashboard-overview',
    authUser,
    'default',
    () => buildDashboardOverview(authUser),
  );
  return c.json(payload);
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

  const candidateRows = getLoginCandidatesByIdentifier(identifier);
  const matchedRows = candidateRows.filter((row) => verifyPassword(password, String(row.password_hash || '')));
  if (!matchedRows.length) {
    return c.json({ error: 'Invalid credentials.' }, 401);
  }

  const uniqueLoginEmails = Array.from(new Set(matchedRows.map((row) => getUserLoginEmail(row)).filter(Boolean)));
  if (uniqueLoginEmails.length > 1) {
    return c.json({ error: 'Multiple accounts matched this name. Please sign in using the email address.' }, 409);
  }

  if (matchedRows.length > 1) {
    const loginEmail = getUserLoginEmail(matchedRows[0]);
    const options = buildRoleSelectionOptions(matchedRows);
    const appConfig = getAppConfig();
    if (isLoginOtpRequiredForUser(matchedRows[0] as Record<string, unknown>, appConfig)) {
      if (getSmtpStatus().state !== 'ready') {
        return c.json({ error: 'SMTP is not ready. Login OTP delivery is unavailable.' }, 400);
      }
      const otpCode = generateOtpCode();
      const sent = await sendOtpEmail(loginEmail, 'Login', otpCode);
      if (!sent) {
        return c.json({ error: 'Unable to send login OTP. Verify SMTP settings and try again.' }, 400);
      }
      const token = randomUUID();
      pendingLoginOtpChallenges.set(token, {
        email: String(matchedRows[0].email || '').trim().toLowerCase(),
        loginEmail,
        role: String(matchedRows[0].role || '').trim().toLowerCase(),
        identifier,
        displayName: String(matchedRows[0].name || loginEmail || identifier).trim(),
        accountEmails: options.map((item) => String(item.accountEmail || '').trim().toLowerCase()).filter(Boolean),
        roleSelectionOptions: options,
        forceLogoutOthers: forceLogout,
        otpHash: hashOtp(otpCode),
        expiresAt: nowMs() + OTP_EXPIRY_MS,
        requestedAt: nowMs(),
        invalidAttempts: 0,
      });
      setChallengeCookie(c, LOGIN_OTP_COOKIE, token);
      return c.json({
        success: true,
        requiresOtp: true,
        maskedEmail: maskEmailAddress(loginEmail),
      });
    }

    createLoginRoleSelectionChallenge(c, {
      identifier,
      loginEmail,
      authMethod: 'password',
      forceLogoutOthers: forceLogout,
      displayName: String(matchedRows[0].name || loginEmail || identifier).trim(),
      options,
      otpVerified: false,
    });
    return c.json({
      success: true,
      requiresRoleSelection: true,
      authMethod: 'password',
      loginEmail,
      options,
    });
  }

  const result = await beginResolvedLogin(c, matchedRows[0] as Record<string, unknown>, {
    forceLogoutOthers: forceLogout,
    authMethod: 'password',
  });
  return c.json(result.payload, result.status as 200 | 400 | 403 | 409 | 423);
});

app.get('/api/auth/login/role-selection', (c) => {
  const state = readLoginRoleSelectionChallenge(c);
  if (!state) {
    return c.json({ error: 'Role selection session expired. Please sign in again.' }, 400);
  }
  return c.json({
    success: true,
    requiresRoleSelection: true,
    authMethod: state.challenge.authMethod,
    loginEmail: state.challenge.loginEmail,
    options: state.challenge.options,
  });
});

app.post('/api/auth/login/select-role', async (c) => {
  const body = (await c.req.json<{ account_email?: string; forceLogout?: boolean }>().catch(() => ({}))) as {
    account_email?: string;
    forceLogout?: boolean;
  };
  const accountEmail = String(body.account_email || '').trim().toLowerCase();
  const forceLogout = Boolean(body.forceLogout);
  const state = readLoginRoleSelectionChallenge(c);
  if (!state) {
    return c.json({ error: 'Role selection session expired. Please sign in again.' }, 400);
  }
  if (!accountEmail) {
    return c.json({ error: 'Select a role to continue.' }, 400);
  }
  const selected = state.challenge.options.find((item) => item.accountEmail === accountEmail);
  if (!selected) {
    return c.json({ error: 'Selected role is no longer available. Please sign in again.' }, 404);
  }
  const userRow = getUserByEmail(accountEmail);
  if (!userRow) {
    clearLoginRoleSelectionChallenge(c, state.token);
    return c.json({ error: 'Selected account was not found. Please sign in again.' }, 404);
  }
  const result = await beginResolvedLogin(c, userRow, {
    forceLogoutOthers: forceLogout || state.challenge.forceLogoutOthers,
    authMethod: state.challenge.authMethod,
    skipOtp: Boolean(state.challenge.otpVerified),
  });
  const shouldKeepRoleSelectionChallenge =
    Number(result.status || 0) === 409
    && Boolean((result.payload as Record<string, unknown> | null | undefined)?.requiresForceLogout);
  if (!shouldKeepRoleSelectionChallenge && (!result.payload || !(result.payload as Record<string, unknown>).requiresRoleSelection)) {
    clearLoginRoleSelectionChallenge(c, state.token);
  }
  return c.json(result.payload, result.status as 200 | 400 | 403 | 409 | 423);
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
    const invalidAttempts = Number(challenge.invalidAttempts || 0) + 1;
    if (invalidAttempts >= 3) {
      pendingLoginOtpChallenges.delete(token);
      clearChallengeCookie(c, LOGIN_OTP_COOKIE);
      const appConfig = getAppConfig();
      const lockHours = getOtpLockHours(appConfig);
      for (const accountEmail of (challenge.accountEmails || [challenge.email])) {
        lockUserForDuration(String(accountEmail || '').trim().toLowerCase(), 'password_unauthorized', lockHours * 60 * 60 * 1000);
      }
      recordAuthFailureAttempt({
        email: challenge.loginEmail || challenge.email,
        ip_address: c.req.header('x-forwarded-for') || c.req.header('x-real-ip') || '',
        user_agent: c.req.header('user-agent') || '',
        auth_method: 'password_failed',
        failure_code: 'password_unauthorized',
        failure_reason: 'Account locked for repeated invalid login OTP attempts. Contact system admin for unblock.',
      });
      return c.json(
        { error: `Too many invalid OTP attempts. This account is locked for ${formatHoursLabel(lockHours)}. Please contact system admin for unblock.` },
        423,
      );
    }
    pendingLoginOtpChallenges.set(token, { ...challenge, invalidAttempts });
    return c.json({ error: 'Invalid OTP. Please try again.' }, 401);
  }
  if ((challenge.roleSelectionOptions || []).length > 1) {
    pendingLoginOtpChallenges.delete(token);
    clearChallengeCookie(c, LOGIN_OTP_COOKIE);
    createLoginRoleSelectionChallenge(c, {
      identifier: String(challenge.identifier || challenge.loginEmail || challenge.email || '').trim(),
      loginEmail: String(challenge.loginEmail || challenge.email || '').trim(),
      authMethod: 'password',
      forceLogoutOthers: Boolean(challenge.forceLogoutOthers),
      displayName: String(challenge.displayName || challenge.loginEmail || challenge.email || '').trim(),
      options: challenge.roleSelectionOptions || [],
      otpVerified: true,
    });
    return c.json({
      success: true,
      requiresRoleSelection: true,
      authMethod: 'password',
      loginEmail: String(challenge.loginEmail || challenge.email || '').trim(),
      options: challenge.roleSelectionOptions || [],
    });
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

app.post('/api/auth/google/resolve-conflict', async (c) => {
  const token = getCookie(c, GOOGLE_LOGIN_CONFLICT_COOKIE) || '';
  cleanupExpiredChallengeMap(pendingGoogleLoginConflictChallenges);
  const challenge = token ? pendingGoogleLoginConflictChallenges.get(token) : null;
  if (!challenge || !isOtpCookieFresh(challenge)) {
    if (token) pendingGoogleLoginConflictChallenges.delete(token);
    clearChallengeCookie(c, GOOGLE_LOGIN_CONFLICT_COOKIE);
    return c.json({ error: 'Google sign-in session expired. Please try again.' }, 400);
  }

  const userRow = getUserByEmail(String(challenge.email || '').trim().toLowerCase());
  pendingGoogleLoginConflictChallenges.delete(token);
  clearChallengeCookie(c, GOOGLE_LOGIN_CONFLICT_COOKIE);

  if (!userRow) {
    return c.json({ error: 'Account not registered.' }, 404);
  }

  const result = await beginResolvedLogin(c, userRow, {
    forceLogoutOthers: true,
    authMethod: 'google',
  });
  if (result.status !== 200) {
    return c.json(result.payload, result.status as 400 | 403 | 409 | 423);
  }
  clearChallengeCookie(c, LOGIN_OTP_COOKIE);
  clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
  clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
  return c.json(result.payload);
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
  clearLoginRoleSelectionChallenge(c);
  return c.json({ success: true });
});

app.post('/api/auth/logout', (c) => {
  const sessionId = c.get('sessionId') || getCookie(c, SESSION_COOKIE) || '';
  if (sessionId) {
    releaseTestModeBlockForAdminSession(String(sessionId));
    logoutSession(sessionId, 'logout');
  }
  deleteCookie(c, SESSION_COOKIE, { path: '/' });
  deleteCookie(c, TEST_MODE_COOKIE, { path: '/' });
  clearChallengeCookie(c, LOGIN_OTP_COOKIE);
  clearLoginRoleSelectionChallenge(c);
  clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
  clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
  return c.json({ success: true });
});

app.get('/api/auth/switch-role/options', (c) => {
  const authUser = c.get('authUser') || null;
  const sessionAuthUser = c.get('sessionAuthUser') || authUser || null;
  const testModeTarget = c.get('testModeTarget') || null;
  const archiveView = c.get('archiveView') || null;
  if (!authUser || !sessionAuthUser) return c.json({ error: 'Unauthorized' }, 401);
  if (testModeTarget) return c.json({ error: 'Exit test mode before switching roles.' }, 400);
  if (archiveView) return c.json({ error: 'Exit archive view before switching roles.' }, 400);
  return c.json({
    success: true,
    options: getAvailableRoleSwitchOptionsForUser(sessionAuthUser),
  });
});

app.post('/api/auth/switch-role', async (c) => {
  const authUser = c.get('authUser') || null;
  const sessionAuthUser = c.get('sessionAuthUser') || authUser || null;
  const testModeTarget = c.get('testModeTarget') || null;
  const archiveView = c.get('archiveView') || null;
  const sessionId = String(c.get('sessionId') || getCookie(c, SESSION_COOKIE) || '').trim();
  if (!authUser || !sessionAuthUser) return c.json({ error: 'Unauthorized' }, 401);
  if (testModeTarget) return c.json({ error: 'Exit test mode before switching roles.' }, 400);
  if (archiveView) return c.json({ error: 'Exit archive view before switching roles.' }, 400);
  if (!sessionId) return c.json({ error: 'Session is unavailable.' }, 400);

  const body = (await c.req.json<{ account_email?: string }>().catch(() => ({}))) as { account_email?: string };
  const accountEmail = String(body.account_email || '').trim().toLowerCase();
  if (!accountEmail) {
    return c.json({ error: 'Select a role to continue.' }, 400);
  }

  const options = getAvailableRoleSwitchOptionsForUser(sessionAuthUser);
  if (options.length < 2) {
    return c.json({ error: 'No alternate roles are available for this login.' }, 400);
  }
  const selected = options.find((item) => item.accountEmail === accountEmail);
  if (!selected) {
    return c.json({ error: 'Selected role is not available for this login.' }, 404);
  }
  if (accountEmail === String(sessionAuthUser.email || '').trim().toLowerCase()) {
    return c.json({ success: true, user: sessionAuthUser });
  }

  const targetUser = getUserByEmail(accountEmail);
  if (!targetUser) {
    return c.json({ error: 'Selected account was not found.' }, 404);
  }
  const sessionLoginEmail = String(sessionAuthUser.login_email || sessionAuthUser.email || '').trim().toLowerCase();
  if (getUserLoginEmail(targetUser) !== sessionLoginEmail) {
    return c.json({ error: 'Selected role does not belong to this login.' }, 403);
  }
  const access = checkUserAccess(accountEmail);
  if (!access.allowed) {
    return c.json({ error: access.message }, 403);
  }

  const appConfig = getAppConfig();
  const allowConcurrent = String(appConfig.allow_concurrent_sessions || 'false').trim().toLowerCase() === 'true';
  releaseTestModeBlockForAdminSession(sessionId);
  logoutSession(sessionId, 'logout');
  deleteCookie(c, TEST_MODE_COOKIE, { path: '/' });
  clearChallengeCookie(c, LOGIN_OTP_COOKIE);
  clearLoginRoleSelectionChallenge(c);
  clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
  clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
  clearChallengeCookie(c, GOOGLE_LOGIN_CONFLICT_COOKIE);
  return c.json(finalizeLogin(c, targetUser, !allowConcurrent, 'password'));
});

app.post('/api/test-mode/start', async (c) => {
  const sessionAuthUser = c.get('sessionAuthUser') || c.get('authUser');
  const adminSessionId = String(c.get('sessionId') || getCookie(c, SESSION_COOKIE) || '').trim();
  if (!sessionAuthUser) return c.json({ error: 'Unauthorized' }, 401);
  if (sessionAuthUser.role !== 'admin') return c.json({ error: 'Forbidden' }, 403);
  if (!adminSessionId) return c.json({ error: 'Admin session is unavailable.' }, 400);
  const body = (await c.req.json<{ email?: string }>().catch(() => ({}))) as { email?: string };
  const email = String(body.email || '').trim().toLowerCase();
  if (!email) return c.json({ error: 'User email is required.' }, 400);
  const target = getUserByEmail(email);
  if (!target) return c.json({ error: 'Selected user was not found.' }, 404);
  if (String(target.role || '').trim().toLowerCase() === 'admin') {
    return c.json({ error: 'Admin accounts cannot be opened in test mode.' }, 403);
  }
  const existingBlock = getTestModeBlockForUser(email);
  if (existingBlock && existingBlock.adminSessionId !== adminSessionId) {
    return c.json({ error: 'This account is already being reviewed in test mode.' }, 409);
  }
  forceLogoutUser(email, 'test_mode_preview');
  assignTestModeBlock(adminSessionId, String(sessionAuthUser.email || ''), email);
  setCookie(c, TEST_MODE_COOKIE, email, {
    path: '/',
    httpOnly: true,
    sameSite: 'Lax',
    maxAge: sessionCookieMaxAge(getAppConfig()),
    expires: sessionCookieExpires(getAppConfig()),
  });
  return c.json({ success: true, user: toAuthUser(target) });
});

app.post('/api/test-mode/stop', (c) => {
  const sessionAuthUser = c.get('sessionAuthUser') || c.get('realAuthUser') || c.get('authUser');
  const adminSessionId = String(c.get('sessionId') || getCookie(c, SESSION_COOKIE) || '').trim();
  if (!sessionAuthUser) return c.json({ error: 'Unauthorized' }, 401);
  if (sessionAuthUser.role !== 'admin') return c.json({ error: 'Forbidden' }, 403);
  if (adminSessionId) {
    releaseTestModeBlockForAdminSession(adminSessionId);
  }
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
  const designation = String(body.designation || '').trim();
  const scopePairs = parseScopeValues(Array.isArray(body.scope_pairs) ? body.scope_pairs : []);
  const existingLoginGroup = getUsersByLoginEmail(email);

  if (!name || !email) return c.json({ error: 'Name and email are required.' }, 400);
  if (!isManagedUserEmailAllowed(email)) return c.json({ error: `Only ${getManagedUserAllowedDomain()} email accounts are allowed.` }, 400);
  if (!existingLoginGroup.length && !password) return c.json({ error: 'Password is required for a new email account.' }, 400);
  if (!existingLoginGroup.length && password !== confirmPassword) return c.json({ error: 'Password and confirm password do not match.' }, 400);
  if (!existingLoginGroup.length && password.length < 6) return c.json({ error: 'Password must be at least 6 characters.' }, 400);

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

  const existingRole = existingLoginGroup.find((item) => normalizeUserRole(String(item.role || 'counselor')) === role);
  if (existingRole) return c.json({ error: 'An account with this email already exists for the selected role.' }, 409);

  try {
    const createdUser = createUser(email, password, name, role, createDepartmentValue, createMaxStudents, true, createYearLevel, designation);
    const scopeOwnerEmail = String(createdUser?.email || email).trim().toLowerCase();
    if (role === 'hod' || role === 'deo') {
      setChiefAdminScopes(scopeOwnerEmail, scopePayload.length ? scopePayload : [{ department: createDepartmentValue, year_level: createYearLevel }]);
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
  let requestedDesignation = String(body.designation || target.designation || '').trim();

  if (requestedName) updates.name = requestedName;
  if (requestedPassword) {
    if (requestedPassword.length < 6) return c.json({ error: 'Password must be at least 6 characters.' }, 400);
    updates.password = requestedPassword;
  }
  if (requestedEmail && !isManagedUserEmailAllowed(requestedEmail)) {
    return c.json({ error: `Only ${getManagedUserAllowedDomain()} email accounts are allowed.` }, 400);
  }

  if (authUser.role !== 'admin') {
    requestedRole = normalizeUserRole(String(target.role || 'counselor'));
  } else {
    updates.role = requestedRole;
  }

  const currentLoginEmail = getUserLoginEmail(target);
  const nextLoginEmail = requestedEmail || currentLoginEmail;
  const conflictingRoleUser = getUsersByLoginEmail(nextLoginEmail).find(
    (item) =>
      normalizeUserRole(String(item.role || 'counselor')) === requestedRole &&
      String(item.email || '').trim().toLowerCase() !== originalEmail,
  );
  if (conflictingRoleUser) {
    return c.json({ error: 'An account with this email already exists for the selected role.' }, 409);
  }

  if (requestedRole === 'admin' || requestedRole === 'principal') {
    updates.designation = requestedRole === 'principal' ? (requestedDesignation || 'Higher Official') : '';
    updates.department = '';
    updates.year_level = 1;
    updates.max_students = 500;
    requestedScopes = [];
  } else if (requestedRole === 'hod' || requestedRole === 'deo') {
    updates.designation = '';
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
    updates.designation = '';
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
    if (requestedEmail && requestedEmail !== currentLoginEmail) {
      updates.email = requestedEmail;
    }
    const updatedUser = updateUser(originalEmail, updates);
    const scopeOwnerEmail = String(updatedUser?.email || originalEmail).trim().toLowerCase();
    if (authUser.role === 'admin') {
      if (requestedRole === 'hod' || requestedRole === 'deo') {
        setChiefAdminScopes(scopeOwnerEmail, requestedScopes.length ? requestedScopes : [{ department: requestedDepartment, year_level: requestedYear }]);
      } else {
        setChiefAdminScopes(scopeOwnerEmail, []);
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
  let studentRowsImported = 0;
  let studentSheetFailures = 0;

  for (const item of rows) {
    if (!isManagedUserEmailAllowed(item.email)) {
      skipped += 1;
      continue;
    }

    if (authUser.role === 'deo') {
      const allowed = new Set(authUser.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
      if (!allowed.has(`${item.department}::${yearLevel}`)) {
        skipped += 1;
        continue;
      }
    }

    const existingCounselor = getUsersByLoginEmail(item.email).find(
      (entry) => normalizeUserRole(String(entry.role || 'counselor')) === 'counselor',
    );
    const selectedPassword = oauthEnabled
      ? (bulkPasswordMode === 'override' ? configuredOverridePassword : item.password)
      : (configuredOverridePassword || item.password);
    const hasValidPassword = selectedPassword.length >= 6;
    const shouldLock = item.needs_lock || !hasValidPassword;

    if (!existingCounselor) {
      try {
        const createdUser = createUser(
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
          lockUser(String(createdUser?.email || item.email).trim().toLowerCase(), `Locked after bulk upload. Missing: ${(item.missing_required || []).join(', ') || 'valid password'}`);
          locked += 1;
        }
        if (item.student_list_link) {
          try {
            const studentWorkbook = await downloadGoogleSheetWorkbook(item.student_list_link);
            const students = parseStudentWorkbook(studentWorkbook);
            studentRowsImported += addStudentsBulk(String(createdUser?.email || item.email).trim().toLowerCase(), students);
          } catch {
            studentSheetFailures += 1;
          }
        }
        created += 1;
      } catch {
        skipped += 1;
      }
      continue;
    }

    const payload: Record<string, unknown> = {
      name: item.name || String(existingCounselor.name || item.email),
      role: 'counselor',
      department: item.department,
      year_level: yearLevel,
      max_students: 30,
    };
    if (hasValidPassword) payload.password = selectedPassword;
    updateUser(String(existingCounselor.email || item.email).trim().toLowerCase(), payload);
    if (shouldLock) {
      lockUser(String(existingCounselor.email || item.email).trim().toLowerCase(), `Locked after bulk upload. Missing: ${(item.missing_required || []).join(', ') || 'valid password'}`);
      locked += 1;
    } else {
      unlockUser(String(existingCounselor.email || item.email).trim().toLowerCase());
    }
    if (item.student_list_link) {
      try {
        const studentWorkbook = await downloadGoogleSheetWorkbook(item.student_list_link);
        const students = parseStudentWorkbook(studentWorkbook);
        studentRowsImported += addStudentsBulk(String(existingCounselor.email || item.email).trim().toLowerCase(), students);
      } catch {
        studentSheetFailures += 1;
      }
    }
    updated += 1;
  }

  return c.json({
    success: true,
    message: `Bulk counselor sync completed. Created: ${created}, Updated: ${updated}, Skipped: ${skipped}, Students imported: ${studentRowsImported}${locked ? `. Locked: ${locked}` : ''}${studentSheetFailures ? `. Student sheet failures: ${studentSheetFailures}` : ''}.`,
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
      parent_phone: normalizePhone(String(body.parent_phone || '')) || String(body.parent_phone || ''),
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

app.get('/api/reports/overview', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(authUser.role === 'admin' || authUser.role === 'principal' || authUser.role === 'hod' || authUser.role === 'deo')) {
    return c.json({ error: 'Forbidden' }, 403);
  }

  const filterDept = String(c.req.query('department') || '').trim().toUpperCase();
  const filterYearLevel = Number(c.req.query('year') || 0) || null;
  const payload = await getCachedReadModelPayload(
    'reports-overview',
    authUser,
    JSON.stringify({ department: filterDept, year: filterYearLevel || 0 }),
    () => buildReportsOverviewPayload(authUser, filterDept, filterYearLevel),
  );
  return c.json(payload);
});

app.get('/api/subjects/overview', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const requestedDepartment = String(c.req.query('department') || '').trim().toUpperCase();
  const requestedYear = Number(c.req.query('year') || 0) || null;
  const requestedSemester = String(c.req.query('semester') || '').trim();
  const departments = getVisibleDepartmentsForActor(authUser);
  const yearsByDepartment = getScopedYearsByDepartment(authUser);
  const availableSemesters = ['1', '2'];

  const selectedDepartment =
    requestedDepartment && departments.some((department) => department.code.toUpperCase() === requestedDepartment)
      ? requestedDepartment
      : (departments.length === 1 ? departments[0].code.toUpperCase() : '');

  const availableYears = selectedDepartment
    ? Array.from(new Set(yearsByDepartment.get(selectedDepartment) || [])).sort((a, b) => a - b)
    : [];
  const selectedYear =
    requestedYear && availableYears.includes(requestedYear)
      ? requestedYear
      : (availableYears.length === 1 ? availableYears[0] : null);
  const selectedSemester =
    availableSemesters.includes(requestedSemester)
      ? requestedSemester
      : '';
  const records = selectedDepartment && selectedYear && selectedSemester
    ? listSubjectsForActor(authUser, { department: selectedDepartment, year_level: selectedYear, semester: selectedSemester })
    : [];

  return c.json({
    departments,
    selectedDepartment,
    availableYears,
    selectedYear,
    availableSemesters,
    selectedSemester,
    showDepartmentPicker: !selectedDepartment,
    showYearPicker: !!selectedDepartment && !selectedYear,
    showSemesterPicker: !!selectedDepartment && !!selectedYear && !selectedSemester,
    canManage: authUser.role !== 'principal',
    records,
  });
});

app.post('/api/subjects/parse-sheet', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  const googleSheetLink = String(body.google_sheet_link || '').trim();
  const department = String(body.department || '').trim().toUpperCase();
  if (!googleSheetLink) return c.json({ error: 'Google Sheet link is required.' }, 400);

  try {
    const parsed = await parseGoogleSheetMetadata(googleSheetLink, department);
    return c.json({
      success: true,
      subject_code: parsed.subject_code || '',
      subject_name: parsed.subject_name || '',
      faculty_name: parsed.faculty_name || '',
      faculty_names: parsed.faculty_names || [],
      class_sections: parsed.class_sections || [],
      faculty_allocations: parsed.faculty_allocations || [],
    });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Unable to parse Google Sheet metadata.' }, 400);
  }
});

app.post('/api/subjects', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  const department = String(body.department || '').trim().toUpperCase();
  const yearLevel = Number(body.year_level || 0) || 0;
  const semester = String(body.semester || '').trim() || '1';
  if (!canManageDepartmentYear(authUser, department, yearLevel)) {
    return c.json({ error: 'You can manage subjects only inside your assigned department/year scope.' }, 403);
  }

  let subjectCode = String(body.subject_code || '').trim();
  let subjectName = String(body.subject_name || '').trim();
  let facultyName = String(body.faculty_name || '').trim();
  const googleSheetLink = String(body.google_sheet_link || '').trim();
  const academicStartYear = Number(body.academic_start_year || 0) || 0;
  const academicEndYear = Number(body.academic_end_year || 0) || 0;
  const classSections = Array.isArray(body.class_sections) ? body.class_sections.map((value) => String(value || '').trim().toUpperCase()).filter(Boolean) : [];
  const facultyAllocations = Array.isArray(body.faculty_allocations)
    ? body.faculty_allocations.map((entry) => ({
      faculty_name: String((entry as Record<string, unknown>)?.faculty_name || '').trim(),
      class_sections: Array.isArray((entry as Record<string, unknown>)?.class_sections)
        ? ((entry as Record<string, unknown>).class_sections as unknown[]).map((value) => String(value || '').trim().toUpperCase()).filter(Boolean)
        : [],
    })).filter((entry) => entry.faculty_name)
    : [];

  if (googleSheetLink && (!subjectCode || !subjectName || !facultyName)) {
    try {
      const parsed = await parseGoogleSheetMetadata(googleSheetLink, department);
      if (!subjectCode) subjectCode = parsed.subject_code;
      if (!subjectName) subjectName = parsed.subject_name;
      if (!facultyName) facultyName = parsed.faculty_name;
    } catch (error) {
      if (!subjectCode || !subjectName || !facultyName) {
        return c.json({ error: error instanceof Error ? error.message : 'Unable to parse Google Sheet metadata.' }, 400);
      }
    }
  }
  const combinedClassSections = Array.from(new Set([
    ...classSections,
    ...facultyAllocations.flatMap((entry) => entry.class_sections),
  ]));
  if (combinedClassSections.length && !doClassSectionsMatchDepartment(combinedClassSections, department)) {
    return c.json({ error: `Parsed or allocated classes must match the selected department ${department}.` }, 400);
  }

  try {
    const subject = createSubjectRecord({
      subject_code: subjectCode,
      subject_name: subjectName,
      faculty_name: facultyName,
      google_sheet_link: googleSheetLink,
      department,
      year_level: yearLevel,
      semester,
      academic_start_year: academicStartYear,
      academic_end_year: academicEndYear,
      class_sections: classSections,
      faculty_allocations: facultyAllocations,
    });
    deleteCdpSubjectSnapshot(subject?.id || 0);
    clearCdpStatusCache(subject?.id || null);
    bumpReadModelCacheVersion();
    return c.json({ success: true, subject });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to create subject.' }, 400);
  }
});

app.put('/api/subjects/:id', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const subjectId = Number(c.req.param('id') || 0);
  const subject = getSubjectById(subjectId);
  if (!subject) return c.json({ error: 'Subject not found.' }, 404);
  if (!canManageDepartmentYear(authUser, subject.department, subject.year_level)) {
    return c.json({ error: 'You can manage subjects only inside your assigned department/year scope.' }, 403);
  }

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  let subjectCode = String(body.subject_code || '').trim();
  let subjectName = String(body.subject_name || '').trim();
  let facultyName = String(body.faculty_name || '').trim();
  const googleSheetLink = String(body.google_sheet_link || '').trim();
  const semester = String(body.semester || '').trim() || subject.semester || '1';
  const academicStartYear = Number(body.academic_start_year || subject.academic_start_year || 0) || 0;
  const academicEndYear = Number(body.academic_end_year || subject.academic_end_year || 0) || 0;
  const classSections = Array.isArray(body.class_sections)
    ? body.class_sections.map((value) => String(value || '').trim().toUpperCase()).filter(Boolean)
    : subject.class_sections;
  const facultyAllocations = Array.isArray(body.faculty_allocations)
    ? body.faculty_allocations.map((entry) => ({
      faculty_name: String((entry as Record<string, unknown>)?.faculty_name || '').trim(),
      class_sections: Array.isArray((entry as Record<string, unknown>)?.class_sections)
        ? ((entry as Record<string, unknown>).class_sections as unknown[]).map((value) => String(value || '').trim().toUpperCase()).filter(Boolean)
        : [],
    })).filter((entry) => entry.faculty_name)
    : subject.faculty_allocations;

  if (googleSheetLink && (!subjectCode || !subjectName || !facultyName)) {
    try {
      const parsed = await parseGoogleSheetMetadata(googleSheetLink, subject.department);
      if (!subjectCode) subjectCode = parsed.subject_code;
      if (!subjectName) subjectName = parsed.subject_name;
      if (!facultyName) facultyName = parsed.faculty_name;
    } catch (error) {
      if (!subjectCode || !subjectName || !facultyName) {
        return c.json({ error: error instanceof Error ? error.message : 'Unable to parse Google Sheet metadata.' }, 400);
      }
    }
  }
  const combinedClassSections = Array.from(new Set([
    ...classSections,
    ...facultyAllocations.flatMap((entry) => entry.class_sections),
  ]));
  if (combinedClassSections.length && !doClassSectionsMatchDepartment(combinedClassSections, subject.department)) {
    return c.json({ error: `Parsed or allocated classes must match the selected department ${subject.department}.` }, 400);
  }

  try {
    const updated = updateSubjectRecord(subjectId, {
      subject_code: subjectCode,
      subject_name: subjectName,
      faculty_name: facultyName,
      google_sheet_link: googleSheetLink,
      semester,
      academic_start_year: academicStartYear,
      academic_end_year: academicEndYear,
      class_sections: classSections,
      faculty_allocations: facultyAllocations,
    });
    deleteCdpSubjectSnapshot(subjectId);
    clearCdpStatusCache(subjectId);
    bumpReadModelCacheVersion();
    return c.json({ success: true, subject: updated });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to update subject.' }, 400);
  }
});

app.delete('/api/subjects/:id', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const subjectId = Number(c.req.param('id') || 0);
  const subject = getSubjectById(subjectId);
  if (!subject) return c.json({ error: 'Subject not found.' }, 404);
  if (!canManageDepartmentYear(authUser, subject.department, subject.year_level)) {
    return c.json({ error: 'You can manage subjects only inside your assigned department/year scope.' }, 403);
  }

  deleteSubjectRecord(subjectId);
  deleteCdpSubjectSnapshot(subjectId);
  clearCdpStatusCache(subjectId);
  bumpReadModelCacheVersion();
  return c.json({ success: true });
});

app.get('/api/cdp/overview', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const requestedDepartment = String(c.req.query('department') || '').trim().toUpperCase();
  const requestedYear = Number(c.req.query('year') || 0) || null;
  const requestedSemester = String(c.req.query('semester') || '').trim();
  const requestedSubjectId = Number(c.req.query('subject_id') || 0) || null;
  const payload = await getCachedReadModelPayload(
    'cdp-overview',
    authUser,
    JSON.stringify({
      department: requestedDepartment,
      year: requestedYear || 0,
      semester: requestedSemester,
      subject_id: requestedSubjectId || 0,
    }),
    () => buildCdpOverviewPayload(authUser, {
      requestedDepartment,
      requestedYear,
      requestedSemester,
      requestedSubjectId,
    }),
  );
  return c.json(payload);
});

app.post('/api/cdp/rebuild-scope', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  const requestedDepartment = String(body.department || '').trim().toUpperCase();
  const requestedYear = Number(body.year || 0) || null;
  const requestedSemester = String(body.semester || '').trim();
  const requestedSubjectId = Number(body.subject_id || 0) || null;
  const payload = await rebuildCdpScopeOverviewPayload(authUser, {
    requestedDepartment,
    requestedYear,
    requestedSemester,
    requestedSubjectId,
  });
  return c.json(payload);
});

app.post('/api/cdp/subjects/:id/recheck', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'hod'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const subjectId = Number(c.req.param('id') || 0);
  const subject = getSubjectById(subjectId);
  if (!subject) return c.json({ error: 'Subject not found.' }, 404);
  if (!canManageDepartmentYear(authUser, subject.department, subject.year_level)) {
    return c.json({ error: 'You can recheck subjects only inside your assigned department/year scope.' }, 403);
  }

  clearCdpStatusCache(subjectId);
  try {
    const status = await parseCdpSheetStatus(subject);
    persistCdpSnapshotFromStatus(subject, status);
    bumpReadModelCacheVersion();
    return c.json({ success: true, status });
  } catch (error) {
    persistCdpSnapshotError(subject, error instanceof Error ? error.message : 'Unable to recheck Google Sheet status.');
    bumpReadModelCacheVersion();
    return c.json({ error: error instanceof Error ? error.message : 'Unable to recheck Google Sheet status.' }, 400);
  }
});

app.post('/api/cdp/subjects/:id/sync-students', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const subjectId = Number(c.req.param('id') || 0);
  const subject = getSubjectById(subjectId);
  if (!subject) return c.json({ error: 'Subject not found.' }, 404);
  if (!canManageDepartmentYear(authUser, subject.department, subject.year_level)) {
    return c.json({ error: 'You can sync subjects only inside your assigned department/year scope.' }, 403);
  }

  clearCdpStatusCache(subjectId);
  let status: CdpSubjectStatus | null = null;
  try {
    status = await parseCdpSheetStatus(subject);
    persistCdpSnapshotFromStatus(subject, status);
  } catch {
    status = null;
    persistCdpSnapshotError(subject, 'Unable to parse the selected Google Sheet.');
  }
  bumpReadModelCacheVersion();

  return c.json({
    success: true,
    snapshot: getSubjectScopeSnapshot(subject.department, subject.year_level),
    status,
    message: 'Shine student scope synced for the selected subject.',
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

    const parsedDepartment = String(parsed.testInfo.department || '').trim().toUpperCase();
    if (parsedDepartment && !doesParsedDepartmentMatch(department, parsedDepartment)) {
      return c.json({
        error: `Upload blocked: this marksheet was detected as ${parsedDepartment}, but the selected Reports department is ${department}.`,
      }, 400);
    }

    const parsedStudentDepartments = Array.from(
      new Set(
        (parsed.students || [])
          .map((student) => String(student.department || '').trim().toUpperCase())
          .filter(Boolean),
      ),
    );
    const mismatchedStudentDepartments = parsedStudentDepartments.filter(
      (candidateDepartment) => !doesParsedDepartmentMatch(department, candidateDepartment),
    );
    if (mismatchedStudentDepartments.length) {
      return c.json({
        error: `Upload blocked: student rows belong to ${mismatchedStudentDepartments.join(', ')}, not the selected Reports department ${department}.`,
      }, 400);
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

    if (existing && String(existing.file_hash || '') === fileHash && uploadMode !== 'replace') {
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
    bumpReadModelCacheVersion();

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
  if (authUser.role === 'principal') return c.json({ error: 'Higher Official access is read-only.' }, 403);
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
    overwrite_existing?: boolean;
  }>().catch(() => ({}))) as {
    test_name?: string;
    semester?: string;
    batch_name?: string;
    section?: string;
    overwrite_existing?: boolean;
  };

  const allowedNames = new Set(['IAT 1', 'IAT 2', 'MODEL EXAM']);
  const testName = String(body.test_name || meta.test_name || '').trim().toUpperCase();
  if (!allowedNames.has(testName)) {
    return c.json({ error: 'Test name must be one of: IAT 1, IAT 2, MODEL EXAM.' }, 400);
  }

  const nextSemester = String(body.semester || meta.semester || '').trim();
  const nextBatchName = String(body.batch_name || meta.batch_name || '').trim();
  const existing = findExistingDepartmentYearTest(department, yearLevel, nextSemester, testName, nextBatchName);
  const existingTestId = Number(existing?.test_id || 0) || 0;
  const shouldOverwriteExisting = Boolean(body.overwrite_existing);

  if (existingTestId && existingTestId !== testId && !shouldOverwriteExisting) {
    return c.json({
      error: `A matching ${testName} test already exists in Semester ${nextSemester}. Save again with overwrite confirmation to replace it.`,
      requiresOverwrite: true,
      existingTestId,
    }, 409);
  }

  if (existingTestId && existingTestId !== testId && shouldOverwriteExisting) {
    deleteTest(existingTestId);
  }

  updateTestMetadataFields(testId, {
    test_name: testName,
    semester: nextSemester,
    department,
    batch_name: nextBatchName,
    section: String(body.section || meta.section || '').trim(),
  });
  bumpReadModelCacheVersion();

  return c.json({ success: true, overwrittenExisting: existingTestId && existingTestId !== testId && shouldOverwriteExisting });
});

app.post('/api/tests/:id/marks/update', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role === 'principal') return c.json({ error: 'Higher Official access is read-only.' }, 403);
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
  bumpReadModelCacheVersion();
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
  bumpReadModelCacheVersion();
  return c.json({ success: true, is_blocked: nextValue ? 1 : 0 });
});

app.delete('/api/tests/:id', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (authUser.role === 'principal') return c.json({ error: 'Higher Official access is read-only.' }, 403);
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
  bumpReadModelCacheVersion();
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
  const attachments = getNoticeAttachments(noticeId).map((attachment) => ({
    ...attachment,
    public_url: buildNoticeAttachmentLink(c, attachment.public_token),
  }));
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
  try {
    const form = await c.req.formData();
    const noticeId = Number(form.get('notice_id') || 0) || null;
    const title = String(form.get('notice_title') || '').trim();
    const messageText = String(form.get('notice_message_text') || '').trim();
    const sendToAllRequested = String(form.get('notice_send_to_all') || '') === 'on';
    const deferAttachments = String(form.get('defer_attachments') || '').trim() === '1';
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

    if (!title && !messageText && !uploads.length && !noticeId && !deferAttachments) {
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
    bumpReadModelCacheVersion();

    return c.json({ success: true, noticeId: targetNoticeId });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to save notice attachments.' }, 500);
  }
});

app.post('/api/notices/upload-chunk', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  try {
    const form = await c.req.formData();
    const noticeId = Number(form.get('notice_id') || 0) || 0;
    const uploadId = String(form.get('upload_id') || '').trim();
    const fileName = String(form.get('file_name') || '').trim();
    const mimeType = String(form.get('mime_type') || '').trim();
    const chunkIndex = Number(form.get('chunk_index') || 0) || 0;
    const totalChunks = Number(form.get('total_chunks') || 0) || 0;
    const rawChunk = form.get('chunk');

    if (!noticeId || !uploadId || !fileName || !(rawChunk instanceof File) || rawChunk.size <= 0) {
      return c.json({ error: 'Invalid chunk upload payload.' }, 400);
    }
    if (!Number.isFinite(chunkIndex) || !Number.isFinite(totalChunks) || chunkIndex < 0 || totalChunks <= 0 || chunkIndex >= totalChunks) {
      return c.json({ error: 'Invalid chunk sequencing.' }, 400);
    }
    if (!canFullyManageNotice(authUser, noticeId)) {
      return c.json({ error: 'You do not have permission to edit this notice.' }, 403);
    }

    const tempDir = resolve(NOTICE_UPLOAD_ROOT, '_chunks', `notice_${noticeId}`);
    await mkdir(tempDir, { recursive: true });
    const tempPath = resolve(tempDir, `${uploadId}.part`);
    const chunkBytes = Buffer.from(await rawChunk.arrayBuffer());
    await writeFile(tempPath, chunkBytes, { flag: chunkIndex === 0 ? 'w' : 'a' });

    if (chunkIndex < totalChunks - 1) {
      return c.json({ success: true, completed: false });
    }

    const extension = extname(fileName).slice(0, 12);
    const storedName = `${randomUUID().replace(/-/g, '')}${extension}`;
    const originalName = sanitizeFileName(fileName || storedName);
    const relativePath = `notice_${noticeId}/${storedName}`;
    const absolutePath = resolve(NOTICE_UPLOAD_ROOT, relativePath);
    await mkdir(dirname(absolutePath), { recursive: true });
    await rename(tempPath, absolutePath);
    const finalStats = await stat(absolutePath);
    addNoticeAttachment(noticeId, storedName, originalName, relativePath, mimeType || '', finalStats.size);
    bumpReadModelCacheVersion();
    return c.json({ success: true, completed: true });
  } catch (error) {
    return c.json({ error: error instanceof Error ? error.message : 'Failed to upload notice attachment chunk.' }, 500);
  }
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
  bumpReadModelCacheVersion();
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

async function serveNoticeFileByToken(c: Context) {
  const attachment = getNoticeAttachmentByToken(String(c.req.param('token') || '').trim());
  if (!attachment) return c.text('Not found', 404);
  const bytes = await readFile(resolve(NOTICE_UPLOAD_ROOT, attachment.relative_path)).catch(() => null);
  if (!bytes) return c.text('Not found', 404);
  c.header('Content-Type', attachment.mime_type || 'application/octet-stream');
  c.header('Content-Disposition', `inline; filename=\"${attachment.original_name || 'attachment'}\"`);
  return c.body(bytes);
}

app.get('/notice-files/:token', serveNoticeFileByToken);
app.get('/api/notice-files/:token', serveNoticeFileByToken);

app.get('/api/activity/overview', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const selectedDepartment = String(c.req.query('department') || '').trim().toUpperCase();
  const selectedYear = Number(c.req.query('year') || 0) || null;
  const selectedSemester = String(c.req.query('semester') || '').trim();
  const selectedTestName = String(c.req.query('test_name') || '').trim().toUpperCase();
  const searchQuery = String(c.req.query('q') || '').trim();
  const sortMode = String(c.req.query('sort') || 'pending_first').trim();
  const isStaticDetailRequest = !!(selectedDepartment && selectedYear && ['1', '2'].includes(selectedSemester) && selectedTestName && !searchQuery && sortMode === 'pending_first');
  const payload = await getCachedReadModelPayload(
    'activity-overview',
    authUser,
    JSON.stringify({
      department: selectedDepartment,
      year: selectedYear || 0,
      semester: selectedSemester,
      test_name: selectedTestName,
      q: searchQuery,
      sort: sortMode,
    }),
    () => buildActivityOverviewPayload(authUser, {
      selectedDepartment,
      selectedYear,
      selectedSemester,
      selectedTestName,
      searchQuery,
      sortMode,
    }),
    isStaticDetailRequest ? ACTIVITY_DETAIL_CACHE_TTL_MS : READ_MODEL_CACHE_TTL_MS,
  );
  return c.json(payload);
});

app.post('/api/activity/prefetch', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!['admin', 'principal', 'hod', 'deo'].includes(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const body = (await c.req.json().catch(() => ({}))) as Record<string, unknown>;
  const requestedDepartment = String(body.department || '').trim().toUpperCase();
  const requestedYear = Number(body.year || 0) || null;
  if (!requestedDepartment || !requestedYear) {
    return c.json({ error: 'Department and year are required.' }, 400);
  }

  const scopePayload = buildActivityOverviewPayload(authUser, {
    selectedDepartment: requestedDepartment,
    selectedYear: requestedYear,
    sortMode: 'pending_first',
  });
  if (!scopePayload.selectedDepartment || !scopePayload.selectedYear) {
    return c.json({ error: 'Selected activity scope is not available.' }, 400);
  }

  const entries: Array<ReturnType<typeof buildActivityOverviewPayload>> = [];
  for (const result of scopePayload.prefetchedResults || []) {
    const payload = withReadModelMeta({
      departments: scopePayload.departments,
      selectedDepartment: scopePayload.selectedDepartment,
      availableYears: scopePayload.availableYears,
      selectedYear: scopePayload.selectedYear,
      selectedSemester: result.semester,
      selectedTestName: result.test_name,
      searchQuery: '',
      sortMode: 'pending_first',
      showDepartmentPicker: false,
      showYearPicker: false,
      showSemesterPicker: false,
      testStatus: scopePayload.testStatus,
      prefetchedResults: scopePayload.prefetchedResults || [],
      result,
    });
    entries.push(payload);
  }

  return c.json({
    success: true,
    department: scopePayload.selectedDepartment,
    year: scopePayload.selectedYear,
    prefetched: entries.length,
    entries,
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
  const actingUser = c.get('sessionAuthUser') || c.get('realAuthUser') || authUser;
  if (String(actingUser?.email || '').trim().toLowerCase() === email) {
    return c.json({ error: 'You cannot force logout your own active session from this view.' }, 400);
  }
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

app.post('/api/session/heartbeat', (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  return c.json({ success: true, now: new Date().toISOString() });
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
    archiveView: c.get('archiveView') || null,
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
  const storageMode = getBackupStorageMode();
  let reconnected = false;
  try {
    const preservedSessions = capturePrivilegedSessions();
    checkpointAndCloseDatabase();
    await unlink(`${SHINE_DB_PATH}-wal`).catch(() => undefined);
    await unlink(`${SHINE_DB_PATH}-shm`).catch(() => undefined);
    if (storageMode === 'gdrive') {
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
    if (storageMode === 'gdrive') {
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

app.post('/api/database/archive-view', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!(isSystemAdmin(authUser.role) || isPrincipal(authUser.role))) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ archive_name?: string }>().catch(() => ({}))) as { archive_name?: string };
  const archiveName = String(body.archive_name || '').trim();
  if (!archiveName) return c.json({ error: 'Archive name is required.' }, 400);
  const archiveNames = new Set((await listArchiveFiles()).map((record) => String(record.name || '').trim()));
  if (!archiveNames.has(archiveName)) {
    return c.json({ error: 'Archive file not found.' }, 404);
  }
  setArchiveViewCookie(c, archiveName);
  return c.json({ success: true, reload: true });
});

app.post('/api/database/archive-view/exit', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  clearArchiveViewCookie(c);
  return c.json({ success: true, reload: true });
});

app.post('/api/database/restore-archive', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ archive_name?: string; password?: string }>().catch(() => ({}))) as { archive_name?: string; password?: string };
  const user = getUserByEmail(authUser.email);
  if (!user || !verifyPassword(String(body.password || ''), String(user.password_hash || ''))) {
    return c.json({ error: 'Password verification failed.' }, 403);
  }
  const archiveName = String(body.archive_name || '').trim();
  if (!archiveName) return c.json({ error: 'Archive name is required.' }, 400);
  const storageMode = getBackupStorageMode();
  let reconnected = false;
  try {
    const preservedSessions = capturePrivilegedSessions();
    checkpointAndCloseDatabase();
    await unlink(`${SHINE_DB_PATH}-wal`).catch(() => undefined);
    await unlink(`${SHINE_DB_PATH}-shm`).catch(() => undefined);
    if (storageMode === 'gdrive') {
      const buffer = await downloadDriveFileFromPath(['archives'], archiveName);
      await writeFile(SHINE_DB_PATH, buffer);
      try {
        await writeFile(
          APP_ENV_FILE,
          await downloadDriveFileFromPath(['archives', getArchiveSnapshotDirFromName(archiveName)], '.env'),
        );
      } catch {
        // Older archives may not include rebuild settings.
      }
      if (await findDrivePath(['archives', getArchiveSnapshotDirFromName(archiveName), 'notice_assets'])) {
        await syncDriveDirectoryToLocal(
          ['archives', getArchiveSnapshotDirFromName(archiveName), 'notice_assets'],
          NOTICE_UPLOAD_ROOT,
          { clearFirst: true },
        );
      }
    } else {
      const archivePath = resolve(ARCHIVE_DIR, archiveName);
      const snapshotDir = getBackupSnapshotDir(archivePath);
      await stat(archivePath);
      await copyFile(archivePath, SHINE_DB_PATH);
      try {
        await stat(resolve(snapshotDir, '.env'));
        await copyFile(resolve(snapshotDir, '.env'), APP_ENV_FILE);
      } catch {
        // Older archives may not include rebuild settings.
      }
      try {
        await stat(resolve(snapshotDir, 'notice_assets'));
        await rm(NOTICE_UPLOAD_ROOT, { recursive: true, force: true });
        await cp(resolve(snapshotDir, 'notice_assets'), NOTICE_UPLOAD_ROOT, { recursive: true, force: true });
      } catch {
        // Older archives may not include notice assets.
      }
    }
    reconnectDatabase();
    restorePrivilegedSessions(preservedSessions);
    clearArchiveViewCookie(c);
    if (storageMode === 'gdrive') {
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
    return c.json({ error: error instanceof Error ? error.message : 'Archive restore failed.' }, 400);
  }
});

app.post('/api/database/delete-archive', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<{ archive_name?: string; password?: string }>().catch(() => ({}))) as { archive_name?: string; password?: string };
  const user = getUserByEmail(authUser.email);
  if (!user || !verifyPassword(String(body.password || ''), String(user.password_hash || ''))) {
    return c.json({ error: 'Password verification failed.' }, 403);
  }
  const archiveName = String(body.archive_name || '').trim();
  if (!archiveName) return c.json({ error: 'Archive name is required.' }, 400);
  try {
    if (getBackupStorageMode() === 'gdrive') {
      await deleteDriveFileFromPath(['archives'], archiveName);
      await clearDrivePath(['archives', getArchiveSnapshotDirFromName(archiveName)]).catch(() => undefined);
      await deleteDriveFileFromPath(['archives'], getArchiveSnapshotDirFromName(archiveName)).catch(() => undefined);
    } else {
      const archivePath = resolve(ARCHIVE_DIR, archiveName);
      const snapshotDir = getBackupSnapshotDir(archivePath);
      await stat(archivePath);
      await unlink(archivePath);
      await rm(snapshotDir, { recursive: true, force: true });
    }
    if (String(getCookie(c, ARCHIVE_VIEW_COOKIE) || '').trim() === archiveName) {
      clearArchiveViewCookie(c);
    }
    return c.json({ success: true });
  } catch {
    return c.json({ error: 'Archive file not found.' }, 404);
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
  try {
    if (!(await latestBackupIsRecentEnough())) {
      const appConfig = getAppConfig();
      const baseBatchName = String(appConfig.current_batch_year || '').trim() || getBatchNameForYearLevel(1, appConfig);
      const autoBackupLabel = `preclear_${baseBatchName}_${new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19)}`;
      await performDatabaseBackup(autoBackupLabel, false, true);
    }
    await clearExamDatabaseOnly();
    await rm(NOTICE_UPLOAD_ROOT, { recursive: true, force: true }).catch(() => undefined);
    await mkdir(NOTICE_UPLOAD_ROOT, { recursive: true });
    if (getBackupStorageMode() === 'gdrive') {
      await syncRuntimeDataMirrorToDrive();
    }
    return c.json({ success: true });
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

app.get('/api/config/export', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  let envContent = '';
  try {
    envContent = await readFile(APP_ENV_FILE, 'utf-8');
  } catch {
    envContent = '';
  }
  const exportedAt = new Date().toISOString().replace(/[:]/g, '-');
  const payload = {
    app: APP_NAME,
    version: APP_VERSION,
    exported_at: new Date().toISOString(),
    appConfig: getAppConfig(),
    envContent,
  };
  c.header('Content-Type', 'application/json; charset=utf-8');
  c.header('Content-Disposition', `attachment; filename="shine-config-${exportedAt}.json"`);
  return c.body(JSON.stringify(payload, null, 2));
});

app.post('/api/config/import', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);

  const body = (await c.req.json<Record<string, unknown>>().catch(() => ({}))) as Record<string, unknown>;
  const importedConfigRaw = (body.appConfig && typeof body.appConfig === 'object' ? body.appConfig : {}) as Record<string, unknown>;
  const importedEnvContent = typeof body.envContent === 'string' ? body.envContent : '';
  const importedSettings = Object.fromEntries(
    Object.entries(importedConfigRaw).map(([key, value]) => [String(key || '').trim(), String(value ?? '')]),
  );

  if (!Object.keys(importedSettings).length) {
    return c.json({ error: 'Imported file does not contain any app settings.' }, 400);
  }

  const currentConfig = getAppConfig();
  const currentStorageMode = getBackupStorageMode(currentConfig);
  const mergedConfig = {
    ...currentConfig,
    ...importedSettings,
  };
  const nextStorageMode = getBackupStorageMode(mergedConfig);
  const nextDriveSettings = getGoogleDriveSettings(mergedConfig);

  if (nextStorageMode === 'gdrive' && !nextDriveSettings.enabled) {
    return c.json({ error: 'Imported config enables Google Drive mode but the Drive OAuth details are incomplete.' }, 400);
  }

  try {
    if (currentStorageMode !== nextStorageMode) {
      await migrateStorageArtifacts(currentStorageMode, nextStorageMode, nextDriveSettings);
    }
    updateAppConfigBulk(importedSettings);
    if (importedEnvContent.trim()) {
      await writeFile(APP_ENV_FILE, importedEnvContent, 'utf-8');
    }
  } catch (error) {
    if (currentStorageMode !== nextStorageMode) {
      updateAppConfig('backup_storage_mode', currentStorageMode);
    }
    return c.json({ error: error instanceof Error ? error.message : 'Failed to import configuration.' }, 400);
  }

  let envContent = '';
  try {
    envContent = await readFile(APP_ENV_FILE, 'utf-8');
  } catch {
    envContent = importedEnvContent;
  }

  return c.json({
    appConfig: sanitizeAppConfigForClient(getAppConfig(), authUser),
    envContent,
    smtpStatus: getSmtpStatus(),
    resetUsers: listUsersForActor(authUser),
  });
});

app.get('/api/notifications/state', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  return c.json({ success: true, ...getNotificationStatesForUser(authUser.email) });
});

app.post('/api/notifications/read', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  const body = (await c.req.json<{ keys?: unknown[] }>().catch(() => ({}))) as { keys?: unknown[] };
  updateNotificationStatesForUser(authUser.email, Array.isArray(body.keys) ? body.keys : [], 'read');
  return c.json({ success: true, ...getNotificationStatesForUser(authUser.email) });
});

app.post('/api/notifications/delete', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  const body = (await c.req.json<{ keys?: unknown[] }>().catch(() => ({}))) as { keys?: unknown[] };
  updateNotificationStatesForUser(authUser.email, Array.isArray(body.keys) ? body.keys : [], 'deleted');
  return c.json({ success: true, ...getNotificationStatesForUser(authUser.email) });
});

app.post('/api/config/update', async (c) => {
  const authUser = c.get('authUser');
  if (!authUser) return c.json({ error: 'Unauthorized' }, 401);
  if (!isSystemAdmin(authUser.role)) return c.json({ error: 'Forbidden' }, 403);
  const body = (await c.req.json<Record<string, unknown>>().catch(() => ({}))) as Record<string, unknown>;
  const currentConfig = getAppConfig();
  const currentStorageMode = getBackupStorageMode(currentConfig);
  const currentOtpLoginEnabled = getBooleanConfigValue(currentConfig.require_otp_on_login);

  const timeoutHours = Number(body.session_timeout_hours || 24);
  if (!Number.isFinite(timeoutHours) || timeoutHours < 1 || timeoutHours > 168) {
    return c.json({ error: 'Session timeout must be between 1 and 168 hours.' }, 400);
  }
  const heartbeat = Number(body.session_heartbeat_interval || 30);
  if (!Number.isFinite(heartbeat) || heartbeat < 10 || heartbeat > 120) {
    return c.json({ error: 'Heartbeat interval must be between 10 and 120 seconds.' }, 400);
  }
  const desktopNotificationPollSeconds = Number(body.desktop_notification_poll_seconds || currentConfig.desktop_notification_poll_seconds || currentConfig.desktop_notification_poll_minutes || 30);
  if (!Number.isFinite(desktopNotificationPollSeconds) || desktopNotificationPollSeconds < 10 || desktopNotificationPollSeconds > 3600) {
    return c.json({ error: 'Desktop notification poll must be between 10 and 3600 seconds.' }, 400);
  }
  const notificationPendingThresholdDays = Number(body.notification_pending_threshold_days || currentConfig.notification_pending_threshold_days || 2);
  if (!Number.isFinite(notificationPendingThresholdDays) || notificationPendingThresholdDays < 1 || notificationPendingThresholdDays > 30) {
    return c.json({ error: 'Pending notification threshold must be between 1 and 30 days.' }, 400);
  }
  const otpLoginLockHours = Number(body.otp_login_lock_hours || currentConfig.otp_login_lock_hours || 5);
  if (!Number.isFinite(otpLoginLockHours) || otpLoginLockHours < 1 || otpLoginLockHours > 168) {
    return c.json({ error: 'OTP lockout must be between 1 and 168 hours.' }, 400);
  }

  const settings: Record<string, string> = {
    session_timeout: String(Math.round(timeoutHours) * 3600),
    session_heartbeat_interval: String(Math.round(heartbeat)),
    desktop_notification_poll_seconds: String(Math.round(desktopNotificationPollSeconds)),
    notification_pending_threshold_days: String(Math.round(notificationPendingThresholdDays)),
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
    otp_login_lock_hours: String(Math.round(otpLoginLockHours)),
    counselor_login_otp_enabled: body.require_otp_on_login ? 'true' : 'false',
    notice_copy_as_image: body.notice_copy_as_image ? 'true' : 'false',
    activity_copy_as_image: body.activity_copy_as_image ? 'true' : 'false',
    notice_defaulter_copy_template: String(body.notice_defaulter_copy_template ?? currentConfig.notice_defaulter_copy_template ?? '').replace(/\r\n/g, '\n'),
    activity_defaulter_copy_template: String(body.activity_defaulter_copy_template ?? currentConfig.activity_defaulter_copy_template ?? '').replace(/\r\n/g, '\n'),
    cdp_defaulter_copy_template: String(body.cdp_defaulter_copy_template ?? currentConfig.cdp_defaulter_copy_template ?? '').replace(/\r\n/g, '\n'),
    backup_storage_mode: String(body.backup_storage_mode || currentConfig.backup_storage_mode || 'local').trim().toLowerCase() === 'gdrive' ? 'gdrive' : 'local',
    enable_counselor_batch_send: body.enable_counselor_batch_send ? 'true' : 'false',
    counselor_batch_send_delay_seconds: String(Math.max(1, Math.min(30, Number(body.counselor_batch_send_delay_seconds || currentConfig.counselor_batch_send_delay_seconds || 4) || 4))),
    desktop_send_workspace_enabled: body.desktop_send_workspace_enabled ? 'true' : 'false',
    desktop_send_target_preference: ['default_browser', 'chrome', 'edge', 'whatsapp_desktop'].includes(String(body.desktop_send_target_preference || currentConfig.desktop_send_target_preference || 'default_browser').trim().toLowerCase())
      ? String(body.desktop_send_target_preference || currentConfig.desktop_send_target_preference || 'default_browser').trim().toLowerCase()
      : 'default_browser',
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
  const nextOtpLoginEnabled = settings.require_otp_on_login === 'true';
  if (nextOtpLoginEnabled !== currentOtpLoginEnabled) {
    const adminPassword = String(body.admin_password || '');
    const user = getUserByEmail(authUser.email);
    if (!user || !verifyPassword(adminPassword, String(user.password_hash || ''))) {
      return c.json({ error: 'Admin password verification failed for OTP policy change.' }, 403);
    }
  }

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
  if (nextOtpLoginEnabled !== currentOtpLoginEnabled) {
    logoutAllUsers();
    deleteCookie(c, SESSION_COOKIE, { path: '/' });
    return c.json({ success: true, appConfig: sanitizeAppConfigForClient(getAppConfig(), authUser), smtpStatus: getSmtpStatus(), relogin: true });
  }
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

  const state = createGoogleOauthState();
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
  const cookieStateMatches = !!state && !!expectedState && state === expectedState;
  const storedStateMatches = consumeGoogleOauthState(state);
  if (!cookieStateMatches && !storedStateMatches) {
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

    const userRows = getUsersByLoginEmail(email);
    const userRow = userRows[0] || null;
    if (!userRow) {
      recordOauthLoginAttempt({
        email,
        display_name: String(profile.name || profile.given_name || email).trim(),
        ip_address: c.req.header('x-forwarded-for') || c.req.header('x-real-ip') || '',
        user_agent: c.req.header('user-agent') || '',
        failure_code: 'user_not_linked',
        failure_reason: 'Account not registered.',
      });
      target.searchParams.set('error', 'user_not_linked');
      target.searchParams.set('error_description', 'Account not registered.');
      return c.redirect(target.toString());
    }

    if (userRows.length > 1) {
      createLoginRoleSelectionChallenge(c, {
        identifier: email,
        loginEmail: email,
        authMethod: 'google',
        forceLogoutOthers: false,
        displayName: String(profile.name || profile.given_name || email).trim(),
        options: buildRoleSelectionOptions(userRows as Array<Record<string, unknown>>),
      });
      target.searchParams.set('role_select', '1');
      return c.redirect(target.toString());
    }

    const result = await beginResolvedLogin(c, userRow as Record<string, unknown>, {
      forceLogoutOthers: false,
      authMethod: 'google',
    });
    if (result.status === 409) {
      createGoogleLoginConflictChallenge(c, String(userRow.email || '').trim().toLowerCase());
      const existingSession = (result.payload as Record<string, unknown>).existingSession as Record<string, unknown> | undefined;
      target.searchParams.set('conflict', '1');
      target.searchParams.set('browser', String(existingSession?.browser || 'Unknown'));
      target.searchParams.set('device_type', String(existingSession?.device_type || 'Unknown'));
      target.searchParams.set('ip_address', String(existingSession?.ip_address || 'Unknown'));
      target.searchParams.set('login_time', String(existingSession?.login_time || ''));
      return c.redirect(target.toString());
    }
    if (result.status !== 200) {
      target.searchParams.set('error', result.status === 423 ? 'account_in_test_mode' : 'access_denied');
      target.searchParams.set('error_description', String((result.payload as Record<string, unknown>).error || 'Unable to sign in.'));
      return c.redirect(target.toString());
    }

    clearChallengeCookie(c, LOGIN_OTP_COOKIE);
    clearChallengeCookie(c, PASSWORD_RESET_COOKIE);
    clearChallengeCookie(c, SELF_RESET_OTP_COOKIE);
    clearChallengeCookie(c, GOOGLE_LOGIN_CONFLICT_COOKIE);
    target.searchParams.set('success', '1');
    return c.redirect(target.toString());
  } catch {
    target.searchParams.set('error', 'oauth_callback_failed');
    return c.redirect(target.toString());
  }
});

async function serveDesktopInstallerDownload(c: Context, requestedRelativePath: string) {
  const artifactPath = resolveDesktopInstallerArtifactPath(requestedRelativePath);
  if (!artifactPath) return c.text('Desktop installer file not found.', 404);

  try {
    const fileStat = await stat(artifactPath);
    if (!fileStat.isFile()) return c.text('Desktop installer file not found.', 404);
    const fileData = await readFile(artifactPath);
    c.header('Content-Type', getStaticMimeType(artifactPath));
    c.header('Cache-Control', artifactPath.endsWith('.appinstaller') ? 'no-store' : 'public, max-age=3600');
    c.header('Content-Disposition', `attachment; filename="${artifactPath.split(/[/\\\\]/).pop() || 'download'}"`);
    return new Response(new Uint8Array(fileData));
  } catch {
    return c.text('Desktop installer file not found.', 404);
  }
}

app.get('/downloads/desktop/latest/:fileName', async (c) => {
  return serveDesktopInstallerDownload(c, `latest/${String(c.req.param('fileName') || '').trim()}`);
});

app.get('/downloads/desktop/releases/:version/:fileName', async (c) => {
  return serveDesktopInstallerDownload(
    c,
    `releases/${String(c.req.param('version') || '').trim()}/${String(c.req.param('fileName') || '').trim()}`,
  );
});

app.get('/downloads/desktop/*', async (c) => {
  return serveDesktopInstallerDownload(c, String(c.req.param('*') || '').trim());
});

app.get('*', async (c) => {
  const pathname = decodeURIComponent(new URL(c.req.url).pathname || '/');
  if (pathname.startsWith('/downloads/desktop/')) {
    return serveDesktopInstallerDownload(c, pathname.replace(/^\/downloads\/desktop\/+/i, ''));
  }
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

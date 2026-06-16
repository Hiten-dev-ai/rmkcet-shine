import { ChangeEvent, FormEvent, MouseEvent as ReactMouseEvent, Suspense, lazy, startTransition, useDeferredValue, useEffect, useMemo, useRef, useState } from 'react';
import type { MutableRefObject } from 'react';
import appCrestLogo from '../assets/logo-optimized.png';
import appWordmarkLogo from '../assets/shine-logo-optimized.png';
import {
  archiveAcademicYear,
  getActivityScopeReport,
  downloadActivityScopeReportPdf,
  downloadConfigExport,
  cancelLoginOtp,
  cleanupSessions,
  completePasswordReset,
  createUserAccount,
  createSubject,
  clearExamDatabase,
  createDatabaseBackup,
  createDepartment,
  deleteUserAccount,
  deleteSubject,
  deleteAdminMessage,
  deleteAdminMessages,
  deleteAllCounselorStudentRows,
  deleteArchiveYear,
  deleteCounselorStudentRow,
  deleteDatabaseBackup,
  deleteNoticeRecord,
  deleteNotificationKeys,
  deleteTest as deleteReportTest,
  deleteDepartment,
  forceLogoutSession,
  exitArchiveView,
  getActivityOverview,
  prefetchActivityScope,
  getAdminMessagesOverview,
  getBootstrap,
  getDashboardOverview,
  getConfigOverview,
  getCounselorMessages,
  getCounselorNoticeSendPage,
  getCounselorOverview,
  getCounselorStudentList,
  getCounselorSendPage,
  getCounselorTests,
  getCdpOverview,
  rebuildCdpScope,
  getDatabaseOverview,
  getDepartments,
  getMonitoringOverview,
  getNoticesOverview,
  getNotificationState,
  getLoginRoleSelection,
  getSessionRoleSwitchOptions,
  getReportsOverview,
  getSubjectsOverview,
  parseSubjectSheet,
  getServerConsole,
  getSmtpStatus,
  importConfigPayload,
  markNotificationKeysRead,
  getTestDetail,
  getUsers,
  login,
  logoutAllSessions,
  logout,
  enterArchiveView,
  requestPasswordReset,
  resetUserPassword,
  resendLoginOtp,
  restoreArchiveYear,
  restoreDatabaseBackup,
  runSmtpTest,
  saveTestMarks,
  saveNotice,
  uploadNoticeAttachmentInChunks,
  saveCounselorStudentRow,
  saveTestMeta,
  sendSessionHeartbeat,
  sendSingleNotice,
  sendSingleReport,
  startTestMode,
  lockUserAccount,
  stopTestMode,
  switchSessionRole,
  sendSelfPasswordOtp,
  selectLoginRole,
  toggleDepartment,
  toggleTestBlock,
  unlockUserAccount,
  updateUserAccount,
  updateSelfPassword,
  uploadCounselorStudentList,
  uploadBulkCounselors,
  uploadMarksheet,
  updateConfig,
  updateDepartment,
  updateEnvContent,
  updateSubject,
  verifyLoginOtp,
  verifyPasswordResetOtp,
  resolveGoogleLoginConflict,
} from './api';
import { clearPersistentCacheBucket, readPersistentCacheEntry, seedPersistentCacheEntries, writePersistentCacheEntry } from './readModelCache';
import {
  enterDesktopSendWorkspace,
  exitDesktopSendWorkspace,
  getAvailableDesktopSendTargets,
  getDesktopSendWorkspaceState,
  hideDesktopSendWorkspace,
  closeFloatingSendWindow,
  checkDesktopUpdate,
  getDesktopAppSettings,
  getDesktopConnectivityState,
  onFloatingSendClosed,
  onFloatingSendRequest,
  onOpenDesktopSettings,
  openDesktopSettings,
  openExternalLink,
  openExternalSendTarget,
  reloadCurrentApp,
  resolveDirectServerUrl,
  runtimeConfig,
  saveDesktopAppSettings,
  showFloatingSendWindow,
  showDesktopNotification,
  showDesktopSendWorkspace,
  startGoogleOauth,
  installDesktopUpdate,
} from './runtime';
import type {
  DesktopAppSettings,
  DesktopConnectivityState,
  DesktopSendTargetAvailability,
  DesktopSendTargetPreference,
  DesktopSendWorkspaceState as DesktopEmbeddedWhatsappState,
  DesktopUpdateInfo,
  FloatingSendWindowPayload,
} from './runtime';

const ActivityTab = lazy(() => import('./tabs/ActivityTab'));
const CdpTab = lazy(() => import('./tabs/CdpTab'));
const DashboardTab = lazy(() => import('./tabs/DashboardTab'));
const MessagesTab = lazy(() => import('./tabs/MessagesTab'));
const MonitoringTab = lazy(() => import('./tabs/MonitoringTab'));
const ReportsTab = lazy(() => import('./tabs/ReportsTab'));
const UsersTab = lazy(() => import('./tabs/UsersTab'));

import type {
  ActivityOverviewPayload,
  ActivityScopeReportPayload,
  ActivityScopeReportSection,
  AdminMessagesOverviewPayload,
  AuthUser,
  BootstrapPayload,
  CdpOverviewPayload,
  ConfigOverviewPayload,
  DashboardOverviewPayload,
  CounselorMessageRecord,
  CounselorMessageStats,
  CounselorActivityRow,
  CounselorNoticeSendPagePayload,
  LinkedCounselorNotificationPayload,
  CounselorStudentRecord,
  CounselorSendNoticeRow,
  CounselorOverviewPayload,
  CounselorSendPagePayload,
  CounselorSendReportRow,
  CounselorVisibleTestRecord,
  DatabaseBackupRecord,
  DatabaseOverviewPayload,
  DepartmentRecord,
  MonitoringOverviewPayload,
  NoticeCompletionRow,
  NoticeRecord,
  NoticesOverviewPayload,
  ReportTestRecord,
  ReportsOverviewPayload,
  Role,
  ScopeRow,
  SessionHistoryRecord,
  SessionMonitoringRecord,
  SessionStatisticsRecord,
  SessionConflict,
  ServerConsolePayload,
  SmtpStatusPayload,
  SubjectRecord,
  SubjectsOverviewPayload,
  TestDetailPayload,
  UserRecord,
  UsersOverviewPayload,
  RoleSelectionOption,
} from './types';

const LAST_AUTH_STATE_KEY = 'shine_last_auth_state';
const USER_CREATE_DRAFT_STORAGE_KEY = 'shine_user_create_draft_v1';
const DEFAULT_MANAGED_USER_DOMAIN = 'rmkcet.ac.in';
const SHARED_ROLE_EMAIL_MARKER = '::__shine_role__:';

function normalizeManagedUserEmailClient(value: string) {
  return String(value || '').trim().toLowerCase();
}

function resolveManagedUserDomainClient(config?: { google_oauth_allowed_domain?: string } | null) {
  return String(config?.google_oauth_allowed_domain || DEFAULT_MANAGED_USER_DOMAIN).trim().toLowerCase().replace(/^@/, '') || DEFAULT_MANAGED_USER_DOMAIN;
}

function normalizeSharedRoleDisplayEmail(value: string) {
  const raw = String(value || '').trim().toLowerCase();
  if (!raw) return '';
  const markerIndex = raw.indexOf(SHARED_ROLE_EMAIL_MARKER);
  return markerIndex >= 0 ? raw.slice(0, markerIndex) : raw;
}

function isCurrentRoleSwitchOption(option: RoleSelectionOption, currentUser: AuthUser | null) {
  if (!currentUser) return false;
  const optionEmail = normalizeSharedRoleDisplayEmail(option.accountEmail);
  const currentEmail = normalizeSharedRoleDisplayEmail(currentUser.email);
  return option.role === currentUser.role
    && optionEmail === currentEmail
    && String(option.designation || '').trim() === String(currentUser.designation || '').trim();
}

type LoginState = {
  identifier: string;
  password: string;
  otp_code: string;
  loading: boolean;
  error: string;
  conflict: SessionConflict | null;
  conflictAuthMethod: 'password' | 'google' | null;
};

type LoginOtpState = {
  maskedEmail: string;
};

type LoginRoleSelectionState = {
  authMethod: 'password' | 'google';
  loginEmail: string;
  options: RoleSelectionOption[];
  selectedAccountEmail: string;
};

type ForgotPasswordState = {
  open: boolean;
  stage: 'request' | 'verify' | 'reset';
  identifier: string;
  maskedEmail: string;
  otp_code: string;
  new_password: string;
  confirm_password: string;
  loading: boolean;
  error: string;
};

type SelfPasswordDraft = {
  current_password: string;
  otp_code: string;
  new_password: string;
  confirm_password: string;
};

const ADMIN_TAB_LABELS: Record<string, string> = {
  dashboard: 'Dashboard',
  notices: 'Notices',
  cdp: 'CDP',
  reports: 'Reports',
  activity: 'Counsellor Activity',
  subjects: 'Subjects',
  users: 'Users',
  departments: 'Departments',
  monitoring: 'Session Monitoring',
  messages: 'Message Logs',
  database: 'Database',
  'server-console': 'Server Console',
  config: 'Settings',
};

const DEFAULT_ADMIN_MESSAGES_LIMIT = 300;
const SCOPE_CACHE_TTL_MS = 30 * 1000;
const ADMIN_MESSAGES_LIMIT_STEP = 300;
const RESOURCE_TEMPLATES = [
  {
    key: 'counsellor-list',
    title: 'Counsellor List',
    description: 'Use this sheet to prepare counselor allocation data with the expected Shine column structure.',
    fileName: 'counsellor_list.xlsx',
    href: '/api/footer/templates/counsellor-list',
    icon: 'fa-user-tie',
  },
  {
    key: 'mark-list',
    title: 'Mark List',
    description: 'Use this upload-ready marksheet template for test imports, GPA values, and failed subject fields.',
    fileName: 'mark_list.xlsx',
    href: '/api/footer/templates/mark-list',
    icon: 'fa-table-list',
  },
  {
    key: 'student-list',
    title: 'Student List',
    description: 'Use this sheet to bulk manage counselor student rosters in the rebuild with the right headers.',
    fileName: 'student_list.xlsx',
    href: '/api/footer/templates/student-list',
    icon: 'fa-users',
  },
] as const;

const COUNSELOR_TAB_LABELS: Record<string, string> = {
  'recent-tests': 'Dashboard',
  notices: 'Notices',
  'test-database': 'Reports',
  'message-history': 'Message Logs',
};

type FlashState = {
  type: 'success' | 'error' | 'warning' | 'info';
  message: string;
} | null;

type CopyLineTone = 'title' | 'section' | 'subsection' | 'name' | 'bullet' | 'body' | 'spacer';

type CopyLine = {
  tone: CopyLineTone;
  text: string;
};

type CounselorSendVerifyState = {
  testId: number;
  testName: string;
  appFound: boolean;
  completed: boolean;
  tone: 'neutral' | 'success' | 'error';
  title: string;
  body: string;
};

type CounselorNoticeSendVerifyState = {
  noticeId: number;
  noticeTitle: string;
  appFound: boolean;
  completed: boolean;
  tone: 'neutral' | 'success' | 'error';
  title: string;
  body: string;
};

type SendReturnState = {
  kind: 'report' | 'notice';
  id: number;
  mode: 'web';
  timestamp: number;
};

type CounselorSendMode = 'app' | 'web' | 'embed';

type DesktopSendQueueState = 'opened' | 'sent' | 'skipped' | 'failed';

type DesktopSendPendingTarget = {
  kind: 'report' | 'notice';
  regNo: string;
  studentName: string;
  deliveryToken: string;
  waLink: string;
};

type MissingWhatsappPromptState = {
  kind: 'report' | 'notice';
  id: number;
  title: string;
};

type AppNotificationItem = {
  key: string;
  severity: 'critical' | 'info';
  title: string;
  body: string;
  createdAt: string;
  actionTab?: string;
};

type FieldOrderEntry =
  | { type: 'subject'; label: string; rawKey: string; normalizedKey: string }
  | { type: 'metric'; metricKey: 'failed_subjects' | 'not_attended' | 'gpa'; label: string };

type BackupActionState = {
  kind: 'restore' | 'delete' | 'archive' | 'restore-archive' | 'delete-archive' | 'clear';
  backupName: string;
} | null;

type ConfigPasswordPromptState = {
  nextTab?: string | null;
} | null;

type DepartmentActionState = {
  kind: 'toggle' | 'delete';
  department: DepartmentRecord;
} | null;

type ConfirmDialogState = {
  title: string;
  message: string;
  confirmLabel: string;
  confirmClassName: string;
  iconClassName: string;
  cancelLabel?: string | null;
};

type DatabaseProgressState = {
  title: string;
  body: string;
} | null;

const NOT_ATTENDED_KEYS = new Set(['examnotattended', 'notattended', 'absentcount', 'noofsubjectsabsent']);
const GPA_KEYS = new Set(['gpa', 'cgpa']);
const FAILED_KEYS = new Set(['noofsubjectsfailed', 'failedsubjects', 'failedcount', 'nooffailedsubjects']);
const IGNORED_KEYS = new Set([
  'regno', 'registernumber', 'name', 'studentname', 'department', 'section', 'batch', 'semester',
  'test', 'total', 'overall', 'percentage', 'grade', 'result', 'status', 'parentphone', 'phone',
  'parentemail', 'email', 'sno', 'slno', 'serialno', 'serialnumber', 'rollno',
  'absentees', 'absentee', 'absentstudents', 'attendance', 'att', 'attendence',
]);
const MOBILE_BREAKPOINT = 768;
const MOBILE_UA_RE = /android|iphone|ipad|ipod|mobile/i;
const SEND_RETURN_STATE_KEY = 'shine_send_return_state';
const SEND_RETURN_STATE_MAX_AGE_MS = 30 * 60 * 1000;
const DEFAULT_REPORT_TEMPLATE = `Dear Parent , The Following is the {test_name} Marks Secured in each Course by your son/daughter

REGISTER NUMBER :  {reg_no}
NAME : {student_name}

{subjects_table}

Regards
PRINCIPAL
RMKCET`;

function buildDefaultNoticeMessage(title: string, text: string, attachmentLinks: string) {
  const safeTitle = String(title || '').trim() || 'Notice';
  const safeText = String(text || '').trim();
  const safeLinks = String(attachmentLinks || '').trim();

  let message = `Dear Parent , \nSub : ${safeTitle} \n\n${safeText}`.trim();
  if (safeLinks) {
    message = `${message}\n\nAttachments:\n${safeLinks}`.trim();
  }
  return message;
}

function applyTheme(theme: 'light' | 'dark') {
  document.documentElement.classList.toggle('preload-light-theme', theme === 'light');
  document.body.classList.toggle('light-theme', theme === 'light');
}

function shouldUseBootLoaderOnInitialLoad() {
  try {
    const params = new URLSearchParams(window.location.search);
    if (params.get('auth') === 'google') {
      return params.get('success') === '1';
    }
    return window.localStorage.getItem(LAST_AUTH_STATE_KEY) === 'authenticated';
  } catch {
    return false;
  }
}

function markAuthStateAuthenticated() {
  try {
    window.localStorage.setItem(LAST_AUTH_STATE_KEY, 'authenticated');
    window.sessionStorage.setItem(LAST_AUTH_STATE_KEY, 'authenticated');
  } catch {
    // Ignore storage failures.
  }
}

function clearRememberedAuthState() {
  try {
    window.localStorage.removeItem(LAST_AUTH_STATE_KEY);
    window.sessionStorage.removeItem(LAST_AUTH_STATE_KEY);
  } catch {
    // Ignore storage failures.
  }
}

function applyThemeColors(config: BootstrapPayload['appConfig'] | null) {
  if (!config) return;
  const root = document.documentElement;
  root.style.setProperty('--primary', config.color_primary);
  root.style.setProperty('--primary-d', config.color_primary_dark);
  root.style.setProperty('--secondary', config.color_secondary);
  root.style.setProperty('--accent', config.color_accent);
  root.style.setProperty('--success', config.color_success);
  root.style.setProperty('--warning', config.color_warning);
  root.style.setProperty('--danger', config.color_danger);
  root.style.setProperty('--info', config.color_info);
  root.style.setProperty('--bg-primary', config.color_bg_primary);
  root.style.setProperty('--bg-secondary', config.color_bg_secondary);
  root.style.setProperty('--bg-card', config.color_bg_card);
  root.style.setProperty('--text', config.color_text);
  root.style.setProperty('--text-dim', config.color_text_dim);
  root.style.setProperty('--text-muted', config.color_text_muted);
  root.style.setProperty('--border', config.color_border);
}

function buildFloatingThemeVars(config: BootstrapPayload['appConfig'] | null | undefined): FloatingSendWindowPayload['themeVars'] {
  if (!config) return {};
  return {
    primary: config.color_primary,
    primaryDark: config.color_primary_dark,
    secondary: config.color_secondary,
    accent: config.color_accent,
    success: config.color_success,
    warning: config.color_warning,
    danger: config.color_danger,
    info: config.color_info,
    bgPrimary: config.color_bg_primary,
    bgSecondary: config.color_bg_secondary,
    bgCard: config.color_bg_card,
    text: config.color_text,
    textDim: config.color_text_dim,
    textMuted: config.color_text_muted,
    border: config.color_border,
  };
}

function getTabsForUser(user: AuthUser | null) {
  if (!user) return [];
  if (user.role === 'admin') {
    return ['dashboard', 'notices', 'cdp', 'reports', 'activity', 'subjects', 'users', 'departments', 'monitoring', 'messages', 'server-console', 'database'];
  }
  if (user.role === 'principal') {
    return ['dashboard', 'notices', 'cdp', 'reports', 'activity', 'subjects', 'departments', 'users', 'database'];
  }
  if (user.role === 'hod') {
    return ['dashboard', 'notices', 'cdp', 'reports', 'activity', 'subjects', 'messages'];
  }
  if (user.role === 'deo') {
    return ['reports', 'notices', 'cdp', 'activity', 'subjects', 'users', 'messages'];
  }
  return ['recent-tests', 'notices', 'test-database', 'message-history'];
}

function getDefaultTab(user: AuthUser | null) {
  if (!user) return 'reports';
  if (user.role === 'admin') return 'dashboard';
  if (user.role === 'principal' || user.role === 'hod') return 'dashboard';
  if (user.role === 'deo') return 'reports';
  return 'recent-tests';
}

function buildAcademicYearLabel(startYear: string, endYear: string) {
  const start = String(startYear || '').trim();
  const end = String(endYear || '').trim();
  if (!start || !end) return '';
  return `${start}-${end}`;
}

function getSmtpIndicator(
  config: BootstrapPayload['appConfig'] | null,
  authUi: BootstrapPayload['authUi'] | null,
) {
  const readyFromServer = Boolean(authUi?.smtpReady);
  const hasServer = Boolean(String(config?.smtp_server || '').trim());
  const hasUsername = Boolean(String(config?.smtp_username || '').trim());
  const ready = readyFromServer || (hasServer && hasUsername);
  return ready
    ? { state: 'ready', icon: 'fa-circle-check', label: 'SMTP Ready', detail: 'SMTP is configured and ready for mail flows.' }
    : { state: 'missing', icon: 'fa-circle-xmark', label: 'SMTP Missing', detail: 'SMTP setup is incomplete. Open settings to finish configuration.' };
}

function ScopeBreadcrumb({ icon, items }: { icon: string; items: Array<{ label: string; onClick?: () => void }> }) {
  return (
    <div className="scope-breadcrumb" role="navigation" aria-label="Scope navigation">
      <i className={`fas ${icon}`}></i>
      {items.map((item, index) => (
        <div className="scope-breadcrumb-segment" key={`${item.label}:${index}`}>
          {item.onClick ? (
            <button type="button" className="scope-breadcrumb-link" onClick={item.onClick}>
              {item.label}
            </button>
          ) : (
            <span className="scope-breadcrumb-current">{item.label}</span>
          )}
          {index < items.length - 1 ? <span className="scope-breadcrumb-sep"><i className="fas fa-angle-right"></i></span> : null}
        </div>
      ))}
    </div>
  );
}

function getPageTitle(tab: string, user: AuthUser | null) {
  if (!user) return 'Panel';
  if (user.role === 'counselor') return COUNSELOR_TAB_LABELS[tab] || 'Panel';
  return ADMIN_TAB_LABELS[tab] || 'Panel';
}

function getNavLabel(tab: string, user: AuthUser | null) {
  if (!user) return tab;
  if (user.role === 'counselor') return COUNSELOR_TAB_LABELS[tab] || tab;
  return ADMIN_TAB_LABELS[tab] || tab;
}

function getNavIcon(tab: string) {
  const map: Record<string, string> = {
    dashboard: 'fa-gauge',
    cdp: 'fa-clipboard-list',
    reports: 'fa-file-lines',
    notices: 'fa-bullhorn',
    subjects: 'fa-book-open',
    departments: 'fa-building',
    activity: 'fa-chart-line',
    users: 'fa-users',
    database: 'fa-database',
    monitoring: 'fa-chart-area',
    'server-console': 'fa-terminal',
    messages: 'fa-envelope',
    config: 'fa-cog',
    'recent-tests': 'fa-gauge',
    'test-database': 'fa-file-lines',
    'message-history': 'fa-envelope-open-text',
  };
  return map[tab] || 'fa-circle';
}

function getRoleBadgeLabel(user: AuthUser) {
  if (user.role === 'hod') return 'HoD';
  if (user.role === 'deo') return 'DEO';
  if (user.role === 'principal') return String(user.designation || 'Higher Official').trim().toUpperCase();
  if (user.role === 'counselor') return 'COUNSELOR';
  return 'ADMIN';
}

function getRoleOptionLabel(role: Role, designation?: string | null) {
  if (role === 'admin') return 'System Admin';
  if (role === 'principal') return String(designation || '').trim() || 'Higher Official';
  if (role === 'hod') return 'HoD';
  if (role === 'deo') return 'DEO';
  return 'Counselor';
}

function getRoleBadgeClass(role: Role) {
  if (role === 'admin' || role === 'principal') return 'badge-role-admin';
  if (role === 'hod') return 'badge-role-chief';
  return 'badge-role-counselor';
}

function getFooterSupportHref(user: AuthUser | null) {
  if (!user) return '/assets/doc_admin.pdf';
  if (user.role === 'counselor') return '/assets/doc_counsellor.pdf';
  if (user.role === 'hod' || user.role === 'deo') return '/assets/doc_chief_admin.pdf';
  return '/assets/doc_admin.pdf';
}

function getNotificationStorageKey(user: AuthUser | null) {
  return `shine_notification_seen:${user?.email || 'guest'}`;
}

function getDeletedNotificationStorageKey(user: AuthUser | null) {
  return `shine_notification_deleted:${user?.email || 'guest'}`;
}

function readSeenNotificationKeys(user: AuthUser | null) {
  if (typeof window === 'undefined') return new Set<string>();
  try {
    return new Set(JSON.parse(window.localStorage.getItem(getNotificationStorageKey(user)) || '[]') as string[]);
  } catch {
    return new Set<string>();
  }
}

function writeSeenNotificationKeys(user: AuthUser | null, keys: Iterable<string>) {
  if (typeof window === 'undefined') return;
  const uniqueKeys = Array.from(new Set(Array.from(keys).map((key) => String(key || '').trim()).filter(Boolean))).slice(-200);
  window.localStorage.setItem(getNotificationStorageKey(user), JSON.stringify(uniqueKeys));
}

function readDeletedNotificationKeys(user: AuthUser | null) {
  if (typeof window === 'undefined') return new Set<string>();
  try {
    return new Set(JSON.parse(window.localStorage.getItem(getDeletedNotificationStorageKey(user)) || '[]') as string[]);
  } catch {
    return new Set<string>();
  }
}

function writeDeletedNotificationKeys(user: AuthUser | null, keys: Iterable<string>) {
  if (typeof window === 'undefined') return;
  const uniqueKeys = Array.from(new Set(Array.from(keys).map((key) => String(key || '').trim()).filter(Boolean))).slice(-300);
  window.localStorage.setItem(getDeletedNotificationStorageKey(user), JSON.stringify(uniqueKeys));
}

function normalizeNotificationKeys(keys: unknown) {
  return Array.from(new Set(
    (Array.isArray(keys) ? keys : [])
      .map((key) => String(key || '').trim())
      .filter(Boolean),
  ));
}

function mergeNotificationState(
  ...states: Array<{ readKeys?: unknown; deletedKeys?: unknown } | null | undefined>
) {
  const readKeys = new Set<string>();
  const deletedKeys = new Set<string>();
  for (const state of states) {
    for (const key of normalizeNotificationKeys(state?.readKeys)) readKeys.add(key);
    for (const key of normalizeNotificationKeys(state?.deletedKeys)) {
      deletedKeys.add(key);
      readKeys.add(key);
    }
  }
  return {
    readKeys: Array.from(readKeys).slice(-500),
    deletedKeys: Array.from(deletedKeys).slice(-500),
  };
}

function compareVersionStrings(left: string, right: string) {
  const leftParts = String(left || '0.0.0').split(/[.-]/).map((part) => Number.parseInt(part, 10) || 0);
  const rightParts = String(right || '0.0.0').split(/[.-]/).map((part) => Number.parseInt(part, 10) || 0);
  const length = Math.max(leftParts.length, rightParts.length);
  for (let index = 0; index < length; index += 1) {
    const diff = (leftParts[index] || 0) - (rightParts[index] || 0);
    if (diff !== 0) return diff;
  }
  return 0;
}

function getWeekdayKey(date = new Date()) {
  return ['sunday', 'monday', 'tuesday', 'wednesday', 'thursday', 'friday', 'saturday'][date.getDay()];
}

function notificationTimestamp(value: string) {
  const parsed = Date.parse(String(value || '').replace(' ', 'T'));
  return Number.isFinite(parsed) ? parsed : 0;
}

function buildAppNotifications(
  user: AuthUser | null,
  pendingNotices: NoticeRecord[],
  assignedTests: CounselorVisibleTestRecord[],
  options: {
    pendingThresholdDays: number;
    updateInfo?: DesktopUpdateInfo | null;
    appVersion?: string;
    desktopSettings?: DesktopAppSettings | null;
    activityRows?: CounselorActivityRow[];
    linkedCounselorNotifications?: LinkedCounselorNotificationPayload | null;
  },
) {
  if (!user) return [] as AppNotificationItem[];
  const notifications: AppNotificationItem[] = [];
  const nowMs = Date.now();
  const pendingThresholdMs = Math.max(1, Number(options.pendingThresholdDays || 2) || 2) * 24 * 60 * 60 * 1000;
  if (options.updateInfo?.available && options.updateInfo.version) {
    notifications.push({
      key: `update:${options.updateInfo.version}`,
      severity: 'critical',
      title: 'Update released',
      body: `Shine ${options.updateInfo.version} is available.`,
      createdAt: new Date().toISOString(),
      actionTab: user.role === 'admin' ? 'config' : undefined,
    });
  }
  if (user.role === 'counselor') {
    for (const test of assignedTests || []) {
      const uploadedAt = String(test.uploaded_at || '');
      const pendingCount = Math.max(0, Number(test.student_count || 0) - Number(test.generated_count || 0));
      if (pendingCount <= 0) continue;
      const isOldPending = pendingCount > 0 && uploadedAt && nowMs - (Date.parse(uploadedAt.replace(' ', 'T')) || nowMs) >= pendingThresholdMs;
      notifications.push({
        key: `test-assigned:${test.test_id || test.id}`,
        severity: 'info',
        title: 'Test assigned',
        body: `${test.test_name} ${formatSemesterBadge(test.semester)} is available for ${test.department} ${formatYearLevel(test.year_level || 1)}.`,
        createdAt: uploadedAt,
        actionTab: 'test-database',
      });
      if (isOldPending) {
        notifications.push({
          key: `test-pending-old:${test.test_id || test.id}`,
          severity: 'critical',
          title: 'Pending reminder',
          body: `${test.test_name} has ${pendingCount} pending student${pendingCount === 1 ? '' : 's'} for more than ${Math.max(1, Number(options.pendingThresholdDays || 2) || 2)} days.`,
          createdAt: uploadedAt,
          actionTab: 'test-database',
        });
      }
    }
    for (const notice of pendingNotices || []) {
      const noticeTitle = String(notice.title_display || notice.title || 'Notice pending').trim();
      const createdAt = String(notice.created_at || '');
      const isOldPending = createdAt && nowMs - (Date.parse(createdAt.replace(' ', 'T')) || nowMs) >= pendingThresholdMs;
      notifications.push({
        key: `notice-assigned:${notice.id}`,
        severity: 'critical',
        title: 'Notice assigned',
        body: noticeTitle,
        createdAt,
        actionTab: 'notices',
      });
      if (isOldPending) {
        notifications.push({
          key: `notice-pending-old:${notice.id}`,
          severity: 'critical',
          title: 'Pending reminder',
          body: `${noticeTitle} has been pending for more than ${Math.max(1, Number(options.pendingThresholdDays || 2) || 2)} days.`,
          createdAt,
          actionTab: 'notices',
        });
      }
    }
  }
  if (user.role !== 'counselor' && options.linkedCounselorNotifications) {
    const linked = options.linkedCounselorNotifications;
    const counselorLabel = [linked.user.department, formatYearLevel(linked.user.year_level || 1)]
      .filter(Boolean)
      .join(' ');
    for (const test of linked.tests || []) {
      const uploadedAt = String(test.uploaded_at || '');
      const pendingCount = Math.max(0, Number(test.student_count || 0) - Number(test.generated_count || 0));
      if (pendingCount <= 0) continue;
      const isOldPending = uploadedAt && nowMs - (Date.parse(uploadedAt.replace(' ', 'T')) || nowMs) >= pendingThresholdMs;
      notifications.push({
        key: `linked-counselor:test-assigned:${linked.user.email}:${test.test_id || test.id}`,
        severity: isOldPending ? 'critical' : 'info',
        title: 'Counselor role: test pending',
        body: `${test.test_name} has ${pendingCount} pending student${pendingCount === 1 ? '' : 's'}${counselorLabel ? ` for ${counselorLabel}` : ''}. Switch to counselor role to send it.`,
        createdAt: uploadedAt,
      });
    }
    for (const notice of linked.overview?.pendingNotices || []) {
      const noticeTitle = String(notice.title_display || notice.title || 'Notice pending').trim();
      const createdAt = String(notice.created_at || '');
      const isOldPending = createdAt && nowMs - (Date.parse(createdAt.replace(' ', 'T')) || nowMs) >= pendingThresholdMs;
      notifications.push({
        key: `linked-counselor:notice-assigned:${linked.user.email}:${notice.id}`,
        severity: isOldPending ? 'critical' : 'info',
        title: 'Counselor role: notice pending',
        body: `${noticeTitle}${counselorLabel ? ` is waiting for ${counselorLabel}` : ' is waiting'}. Switch to counselor role to send it.`,
        createdAt,
      });
    }
  }
  if ((user.role === 'hod' || user.role === 'principal') && options.desktopSettings && runtimeConfig.isDesktop) {
    const digestDay = String(options.desktopSettings.higherOfficialDigestDay || 'monday').toLowerCase();
    if (digestDay === getWeekdayKey()) {
      const pendingRows = (options.activityRows || []).filter((row) => Number(row.pending_count || 0) > 0);
      const scopeRows = options.desktopSettings.higherOfficialDigestScope === 'all'
        ? pendingRows
        : pendingRows.filter((row) => user.scopes.some((scope) => scope.department === row.department && Number(scope.year_level) === Number(row.year_level)));
      if (scopeRows.length) {
        notifications.push({
          key: `digest:${new Date().toISOString().slice(0, 10)}:${options.desktopSettings.higherOfficialDigestScope}:${scopeRows.length}`,
          severity: 'critical',
          title: 'Pending counselor digest',
          body: `${scopeRows.length} counselor${scopeRows.length === 1 ? '' : 's'} have pending work in ${options.desktopSettings.higherOfficialDigestScope === 'all' ? 'all scopes' : 'your allocated scope'}.`,
          createdAt: new Date().toISOString(),
          actionTab: 'activity',
        });
      }
    }
  }
  return notifications.sort((left, right) => notificationTimestamp(right.createdAt) - notificationTimestamp(left.createdAt));
}

function shouldRestoreSendReturnState() {
  try {
    const referrer = String(document.referrer || '').toLowerCase();
    if (referrer.includes('web.whatsapp.com') || referrer.includes('wa.me')) return true;
    const [entry] = performance.getEntriesByType('navigation') as PerformanceNavigationTiming[];
    return entry?.type === 'back_forward';
  } catch {
    return false;
  }
}

function SmartDateInput({
  value,
  onChange,
  placeholder = '09 Jun 2026',
  id,
}: {
  value: string;
  onChange: (nextValue: string) => void;
  placeholder?: string;
  id?: string;
}) {
  const [dateMode, setDateMode] = useState(Boolean(value));
  const inputRef = useRef<HTMLInputElement | null>(null);

  useEffect(() => {
    if (value) {
      setDateMode(true);
      return;
    }
    setDateMode(false);
  }, [value]);

  return (
    <div className="smart-date-input-shell">
      <input
        id={id}
        ref={inputRef}
        className="form-control smart-date-input"
        type={dateMode ? 'date' : 'text'}
        value={value}
        placeholder={dateMode ? undefined : placeholder}
        onFocus={() => setDateMode(true)}
        onBlur={() => {
          if (!value) setDateMode(false);
        }}
        onChange={(event) => onChange(event.target.value)}
      />
      {!dateMode ? (
        <button
          type="button"
          className="smart-date-input-trigger"
          aria-label="Open date picker"
          onClick={() => {
            setDateMode(true);
            window.requestAnimationFrame(() => {
              const element = inputRef.current;
              if (!element) return;
              element.focus();
              if ('showPicker' in element && typeof element.showPicker === 'function') {
                element.showPicker();
              }
            });
          }}
        >
          <i className="fas fa-calendar-alt"></i>
        </button>
      ) : null}
    </div>
  );
}

function loginConflictHasUnknownDetails(conflict: SessionConflict | null | undefined) {
  if (!conflict) return false;
  const values = [
    conflict.browser,
    conflict.device_type,
    conflict.ip_address,
    conflict.login_time,
  ].map((value) => String(value || '').trim().toLowerCase());
  return values.every((value) => !value || value === 'unknown');
}

function normalizeOtpCode(value: string) {
  return String(value || '').replace(/\D/g, '').slice(0, 6);
}

function formatYearLevel(year: number) {
  if (year === 1) return '1st Year';
  if (year === 2) return '2nd Year';
  if (year === 3) return '3rd Year';
  if (year === 4) return '4th Year';
  return `Year ${year}`;
}

function formatSemesterBadge(semester: string) {
  if (String(semester || '').trim() === '1') return 'Sem - I';
  if (String(semester || '').trim() === '2') return 'Sem - II';
  return `Sem - ${String(semester || '').trim() || '-'}`;
}

const DEFAULT_NOTICE_DEFAULTER_COPY_TEMPLATE = 'The Following Counsellors are yet to send the specified Notices\n\n{entries}';
const DEFAULT_ACTIVITY_DEFAULTER_COPY_TEMPLATE = 'The Following are all the counsellors who are yet to send results to their respective students\n\n{entries}';
const DEFAULT_CDP_DEFAULTER_COPY_TEMPLATE = "The following subjects's CDP is not yet filled ,\n\n{entries}";

function escapeSvgText(value: string) {
  return String(value || '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function renderCopyLinesAsText(lines: CopyLine[]) {
  return lines.map((line) => line.text).join('\n').replace(/\n{3,}/g, '\n\n').trim();
}

function renderCopyTemplate(template: string, values: Record<string, string>) {
  return String(template || '').replace(/\{([a-zA-Z0-9_]+)\}/g, (_, key) => values[key] ?? '');
}

function plainTextToCopyLines(text: string) {
  const rows = String(text || '').replace(/\r\n/g, '\n').split('\n');
  const lines: CopyLine[] = [];
  for (const row of rows) {
    const trimmed = row.trim();
    if (!trimmed) {
      lines.push({ tone: 'spacer', text: '' });
      continue;
    }
    if (trimmed.startsWith('- ')) {
      lines.push({ tone: 'bullet', text: trimmed });
      continue;
    }
    if (trimmed.startsWith('*') && trimmed.endsWith('*') && trimmed.length > 2) {
      lines.push({ tone: 'name', text: trimmed });
      continue;
    }
    lines.push({ tone: 'body', text: row });
  }
  return lines;
}

async function copySvgImageToClipboard(svgMarkup: string) {
  const svgBlob = new Blob([svgMarkup], { type: 'image/svg+xml;charset=utf-8' });
  const url = URL.createObjectURL(svgBlob);
  try {
    const image = await new Promise<HTMLImageElement>((resolve, reject) => {
      const nextImage = new Image();
      nextImage.onload = () => resolve(nextImage);
      nextImage.onerror = () => reject(new Error('Unable to load generated image.'));
      nextImage.src = url;
    });

    const canvas = document.createElement('canvas');
    canvas.width = image.width;
    canvas.height = image.height;
    const context = canvas.getContext('2d');
    if (!context) throw new Error('Canvas is not available.');
    context.drawImage(image, 0, 0);
    const pngBlob = await new Promise<Blob>((resolve, reject) => {
      canvas.toBlob((blob) => {
        if (blob) resolve(blob);
        else reject(new Error('Unable to render PNG.'));
      }, 'image/png');
    });

    await navigator.clipboard.write([
      new ClipboardItem({
        'image/png': pngBlob,
      }),
    ]);
  } finally {
    URL.revokeObjectURL(url);
  }
}

function buildCopyCardSvg(title: string, lines: CopyLine[]) {
  const width = 1200;
  const paddingX = 46;
  const contentWidth = width - (paddingX * 2);
  const baseLineHeight = 22;

  function wrapText(text: string, maxWidth: number, fontSize: number) {
    const normalized = String(text || '').replace(/\s+/g, ' ').trim();
    if (!normalized) return [''];
    const words = normalized.split(' ');
    const linesOut: string[] = [];
    const approxCharWidth = fontSize * 0.56;
    let current = '';

    for (const word of words) {
      const next = current ? `${current} ${word}` : word;
      if ((next.length * approxCharWidth) <= maxWidth) {
        current = next;
      } else {
        if (current) linesOut.push(current);
        current = word;
      }
    }
    if (current) linesOut.push(current);
    return linesOut.length ? linesOut : [''];
  }

  function estimateBlockWidth(linesOut: string[], fontSize: number, horizontalPadding: number) {
    const longest = linesOut.reduce((max, entry) => Math.max(max, entry.length), 0);
    return Math.min(contentWidth, Math.max(180, (longest * fontSize * 0.56) + horizontalPadding));
  }

  function renderWrappedText(x: number, y: number, linesOut: string[], fontSize: number, fontWeight: number | string, fill: string, lineGap = 0) {
    return `<text x="${x}" y="${y}" font-family="Segoe UI, Arial, sans-serif" font-size="${fontSize}" font-weight="${fontWeight}" fill="${fill}">${linesOut
      .map((entry, index) => `<tspan x="${x}" dy="${index === 0 ? 0 : fontSize + lineGap}">${escapeSvgText(entry)}</tspan>`)
      .join('')}</text>`;
  }

  let y = 68;
  const content: string[] = [];

  const bodyLines = lines
    .filter((line) => line.tone === 'body')
    .map((line) => line.text)
    .join(' ');
  if (bodyLines) {
    const wrapped = wrapText(bodyLines, contentWidth - 80, 17);
    const bodyHeight = 28 + (wrapped.length * 24);
    content.push(`<rect x="${paddingX}" y="${y}" width="${contentWidth}" height="${bodyHeight}" rx="20" fill="#f5f9ff" stroke="#d7e5ff" stroke-width="1.5"/>`);
    content.push(renderWrappedText(paddingX + 22, y + 30, wrapped, 17, 600, '#4c5c74', 5));
    y += bodyHeight + 22;
  }

  for (const line of lines) {
    if (line.tone === 'body') continue;
    if (line.tone === 'spacer') {
      y += 8;
      continue;
    }

    if (line.tone === 'section') {
      const labelWidth = Math.min(300, Math.max(170, (line.text.length * 18) + 44));
      content.push(`<rect x="${paddingX}" y="${y}" width="${labelWidth}" height="44" rx="18" fill="#dfe8ff" stroke="#c3d4ff" stroke-width="1.5"/>`);
      content.push(`<text x="${paddingX + 20}" y="${y + 29}" font-family="Segoe UI, Arial, sans-serif" font-size="21" font-weight="800" fill="#2e4b97">${escapeSvgText(line.text)}</text>`);
      y += 52;
      continue;
    }

    if (line.tone === 'subsection') {
      const labelWidth = Math.min(260, Math.max(156, (line.text.length * 15) + 40));
      content.push(`<rect x="${paddingX + 18}" y="${y}" width="${labelWidth}" height="36" rx="14" fill="#ffffff" stroke="#dbe6fb" stroke-width="1.5"/>`);
      content.push(`<text x="${paddingX + 36}" y="${y + 24}" font-family="Segoe UI, Arial, sans-serif" font-size="18" font-weight="700" fill="#486083">${escapeSvgText(line.text)}</text>`);
      y += 44;
      continue;
    }

    if (line.tone === 'name') {
      const displayText = line.text.replace(/\*/g, '');
      const wrapped = wrapText(displayText, contentWidth - 148, 18);
      const boxHeight = 24 + (wrapped.length * 24);
      const boxWidth = Math.min(contentWidth - 18, Math.max(420, estimateBlockWidth(wrapped, 18, 94)));
      content.push(`<rect x="${paddingX + 26}" y="${y}" width="${boxWidth}" height="${boxHeight}" rx="18" fill="#ffffff" stroke="#dce7fa" stroke-width="1.5"/>`);
      content.push(`<circle cx="${paddingX + 58}" cy="${y + (boxHeight / 2)}" r="18" fill="#eef3ff" stroke="#d6e2ff" stroke-width="1.5"/>`);
      content.push(`<image href="${appCrestLogo}" x="${paddingX + 42}" y="${y + (boxHeight / 2) - 16}" width="32" height="32" preserveAspectRatio="xMidYMid meet"/>`);
      content.push(renderWrappedText(paddingX + 88, y + 26, wrapped, 18, 800, '#13233e', 5));
      y += boxHeight + 10;
      continue;
    }

    if (line.tone === 'bullet') {
      const displayText = line.text.replace(/^-+\s*/, '');
      const pendingMatch = displayText.match(/^(.*)\s+\((\d+\s+pending)\)$/i);
      const labelText = pendingMatch ? pendingMatch[1].trim() : displayText;
      const badgeText = pendingMatch ? pendingMatch[2].trim() : '';
      const wrapped = wrapText(labelText, badgeText ? contentWidth - 330 : contentWidth - 180, 17);
      const boxHeight = 22 + (wrapped.length * 22);
      const boxWidth = Math.min(contentWidth - 60, Math.max(440, estimateBlockWidth(wrapped, 17, badgeText ? 210 : 130)));
      const badgeWidth = badgeText ? Math.max(122, (badgeText.length * 9.2) + 28) : 0;
      const bulletX = paddingX + 52;
      content.push(`<rect x="${bulletX}" y="${y}" width="${boxWidth}" height="${boxHeight}" rx="16" fill="#ffffff" stroke="#d8e4fb" stroke-width="1.5"/>`);
      content.push(`<circle cx="${bulletX + 24}" cy="${y + 18}" r="6" fill="#667eea"/>`);
      content.push(renderWrappedText(bulletX + 42, y + 22, wrapped, 17, 700, '#3d5172', 4));
      if (badgeText) {
        content.push(`<rect x="${bulletX + boxWidth - badgeWidth - 16}" y="${y + 10}" width="${badgeWidth}" height="26" rx="13" fill="#eef2ff" stroke="#cfd9ff"/>`);
        content.push(`<text x="${bulletX + boxWidth - (badgeWidth / 2) - 16}" y="${y + 28}" text-anchor="middle" font-family="Segoe UI, Arial, sans-serif" font-size="14" font-weight="800" fill="#5567a6">${escapeSvgText(badgeText)}</text>`);
      }
      y += boxHeight + 10;
    }
  }

  const height = Math.max(300, y + 34);
  const headerBandHeight = 88;
  const rendered: string[] = [
    '<defs>',
    '  <linearGradient id="copyCardPage" x1="0" y1="0" x2="1" y2="1">',
    '    <stop offset="0%" stop-color="#f4f7ff"/>',
    '    <stop offset="100%" stop-color="#ebf2ff"/>',
    '  </linearGradient>',
    '  <linearGradient id="copyCardHeader" x1="0" y1="0" x2="1" y2="0">',
    '    <stop offset="0%" stop-color="#5f73e7"/>',
    '    <stop offset="100%" stop-color="#7a5fe8"/>',
    '  </linearGradient>',
    '  <filter id="copyCardShadow" x="-10%" y="-10%" width="120%" height="130%">',
    '    <feDropShadow dx="0" dy="16" stdDeviation="18" flood-color="#7186b3" flood-opacity="0.18"/>',
    '  </filter>',
    '</defs>',
    `<rect x="12" y="12" width="${width - 24}" height="${height - 24}" rx="30" fill="url(#copyCardPage)" stroke="#d7e1f6" stroke-width="1.5" filter="url(#copyCardShadow)"/>`,
    `<rect x="12" y="12" width="${width - 24}" height="${headerBandHeight}" rx="30" fill="url(#copyCardHeader)"/>`,
    `<rect x="12" y="${headerBandHeight - 8}" width="${width - 24}" height="${height - headerBandHeight - 4}" rx="26" fill="url(#copyCardPage)"/>`,
    `<circle cx="${paddingX + 28}" cy="52" r="24" fill="#ffffff" fill-opacity="0.98"/>`,
    `<image href="${appCrestLogo}" x="${paddingX + 8}" y="32" width="40" height="40" preserveAspectRatio="xMidYMid meet"/>`,
    `<text x="${paddingX + 66}" y="58" font-family="Segoe UI, Arial, sans-serif" font-size="31" font-weight="800" fill="#ffffff">${escapeSvgText(title)}</text>`,
    `<text x="${paddingX + 66}" y="82" font-family="Segoe UI, Arial, sans-serif" font-size="14" font-weight="600" fill="#dfe6ff">RMKCET SHINE Share Card</text>`,
    `<rect x="${width - 248}" y="28" width="194" height="46" rx="15" fill="#ffffff" fill-opacity="0.94"/>`,
    `<image href="${appWordmarkLogo}" x="${width - 234}" y="34" width="166" height="34" preserveAspectRatio="xMidYMid meet"/>`,
    ...content,
  ];
  return `<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" viewBox="0 0 ${width} ${height}">${rendered.join('')}</svg>`;
}

function buildNoticeCopyEntries(rows: NoticeCompletionRow[]) {
  const pendingRows = rows
    .filter((row) => (row.pending_notice_count || 0) > 0)
    .sort((a, b) =>
      a.department.localeCompare(b.department)
      || (a.year_level || 1) - (b.year_level || 1)
      || a.name.localeCompare(b.name),
    );
  const lines: string[] = [];
  let lastScope = '';
  for (const row of pendingRows) {
    const scopeKey = `${row.department}::${row.year_level}`;
    if (scopeKey !== lastScope) {
      lines.push(row.department);
      lines.push(formatYearLevel(row.year_level || 1));
      lastScope = scopeKey;
    }
    lines.push(`*${row.name}*`);
    for (const title of row.pending_notice_titles || []) {
      lines.push(`- ${title}`);
    }
    lines.push('');
  }
  return lines.join('\n').trim();
}

function buildActivityCopyEntries(
  sections: ActivityScopeReportSection[],
) {
  const lines: string[] = [];

  const grouped = new Map<string, Map<number, Map<string, Map<string, string[]>>>>();
  for (const section of sections) {
    const pendingRows = section.rows.filter((row) => Number(row.pending_count || 0) > 0);
    if (!pendingRows.length) continue;
    if (!grouped.has(section.department)) grouped.set(section.department, new Map());
    const yearMap = grouped.get(section.department)!;
    if (!yearMap.has(section.year_level)) yearMap.set(section.year_level, new Map());
    const semesterMap = yearMap.get(section.year_level)!;
    if (!semesterMap.has(section.semester)) semesterMap.set(section.semester, new Map());
    const counselorMap = semesterMap.get(section.semester)!;

      for (const row of pendingRows) {
        const counselorKey = String(row.email || '').trim().toLowerCase() || row.name;
        if (!counselorMap.has(counselorKey)) counselorMap.set(counselorKey, []);
        counselorMap.get(counselorKey)!.push(
          `${section.test_name} (${Number(row.pending_count || 0)} pending)`,
        );
        if (!counselorMap.has(`__name__:${counselorKey}`)) counselorMap.set(`__name__:${counselorKey}`, [row.name]);
      }
    }

  for (const [department, yearMap] of grouped.entries()) {
    lines.push(department);
    for (const [yearLevel, semesterMap] of yearMap.entries()) {
      lines.push(formatYearLevel(yearLevel));
      for (const [semester, counselorMap] of semesterMap.entries()) {
        lines.push(formatSemesterBadge(semester));
        const counselorEntries = Array.from(counselorMap.entries())
          .filter(([key]) => !key.startsWith('__name__:'))
          .map(([key, tests]) => ({
            name: counselorMap.get(`__name__:${key}`)?.[0] || key,
            tests: Array.from(new Set(tests)),
          }))
          .sort((a, b) => a.name.localeCompare(b.name));
        for (const counselor of counselorEntries) {
          lines.push(`*${counselor.name}*`);
          for (const testName of counselor.tests) {
            lines.push(`- ${testName}`);
          }
        }
        lines.push('');
      }
    }
  }

  return lines.join('\n').trim();
}

function getDefaultBatchNameForYearLevel(year: number, config: BootstrapPayload['appConfig'] | null) {
  const safeYear = Math.max(1, Number(year || 1) || 1);
  const rawBase = String(config?.current_batch_year || '').trim();
  return deriveBatchNameFromBase(rawBase, safeYear);
}

function getUserDepartmentCodes(user: AuthUser | null) {
  const scopedCodes = user?.scopes?.length
    ? user.scopes.map((scope) => String(scope.department || '').trim().toUpperCase()).filter(Boolean)
    : [];
  const fallbackCode = String(user?.department || '').trim().toUpperCase();
  return Array.from(new Set([...(scopedCodes || []), ...(fallbackCode ? [fallbackCode] : [])]));
}

function deriveBatchNameFromBase(rawBase: string, year: number) {
  const safeYear = Math.max(1, Number(year || 1) || 1);
  const match = rawBase.match(/^(\d{4})\s*-\s*(\d{2,4})$/);

  let baseStart = new Date().getFullYear();
  let baseEnd = baseStart + 1;
  if (match) {
    baseStart = Number(match[1]);
    const tail = match[2];
    baseEnd = tail.length === 2 ? Number(`${String(baseStart).slice(0, 2)}${tail}`) : Number(tail);
  }

  const duration = Math.max(1, baseEnd - baseStart);
  const targetStart = baseStart - (safeYear - 1);
  const targetEnd = targetStart + duration;
  return `${targetStart}-${targetEnd}`;
}

function parseAcademicBatchRange(rawBase: string) {
  const match = String(rawBase || '').trim().match(/^(\d{4})\s*-\s*(\d{2,4})$/);
  const currentYear = new Date().getFullYear();
  if (!match) {
    return { startYear: currentYear, endYear: currentYear + 1 };
  }
  const startYear = Number(match[1]);
  const tail = match[2];
  const endYear = tail.length === 2 ? Number(`${String(startYear).slice(0, 2)}${tail}`) : Number(tail);
  return { startYear, endYear };
}

function getDefaultSubjectAttendanceYear() {
  return new Date().getFullYear();
}

function getSemesterLabel(semester: string) {
  return String(semester || '1').trim() === '2' ? 'Sem - II' : 'Sem - I';
}

function looksLikeGoogleSheetLink(value: string) {
  const raw = String(value || '').trim();
  return /^https?:\/\/docs\.google\.com\/spreadsheets\/d\//i.test(raw) || /\/d\/[a-zA-Z0-9-_]+/i.test(raw);
}

function normalizeClassSections(values: string[]) {
  return Array.from(new Set((values || []).map((value) => String(value || '').trim().toUpperCase()).filter(Boolean)));
}

function splitFacultyNames(value: string) {
  return Array.from(new Set(
    String(value || '')
      .split(/(?:\r?\n|\/|;)+/g)
      .map((item) => String(item || '').trim())
      .filter(Boolean),
  ));
}

function normalizeFacultyAllocations(
  allocations: Array<{ faculty_name: string; class_sections: string[] }>,
  facultyNames: string[],
  parsedClasses: string[],
) {
  const allowedClasses = normalizeClassSections(parsedClasses || []);
  const normalizeFacultyKey = (value: string) =>
    String(value || '')
      .trim()
      .toUpperCase()
      .replace(/\./g, '')
      .replace(/[^A-Z0-9]+/g, ' ')
      .replace(/\s+/g, ' ')
      .trim();
  const findBestExistingClasses = (facultyName: string) => {
    const direct = existingMap.get(facultyName);
    if (direct && direct.length) return direct;
    const targetKey = normalizeFacultyKey(facultyName);
    if (!targetKey) return [];
    const targetTokens = targetKey.split(' ').filter(Boolean);
    let bestMatch: string[] = [];
    let bestScore = 0;
    for (const [existingName, existingClasses] of existingMap.entries()) {
      if (!existingClasses.length) continue;
      const existingKey = normalizeFacultyKey(existingName);
      if (!existingKey) continue;
      if (existingKey === targetKey || existingKey.includes(targetKey) || targetKey.includes(existingKey)) {
        return existingClasses;
      }
      const existingTokens = existingKey.split(' ').filter(Boolean);
      const shared = targetTokens.filter((token) =>
        existingTokens.some((existingToken) =>
          existingToken === token
          || existingToken.startsWith(token)
          || token.startsWith(existingToken),
        ),
      ).length;
      if (shared > bestScore) {
        bestScore = shared;
        bestMatch = existingClasses;
      }
    }
    return bestScore >= Math.max(1, Math.min(2, targetTokens.length)) ? bestMatch : [];
  };
  const existingMap = new Map(
    (allocations || []).map((entry) => [
      String(entry.faculty_name || '').trim(),
      normalizeClassSections(entry.class_sections || []).filter((value) => allowedClasses.includes(value)),
    ]),
  );
  return facultyNames
    .map((facultyName) => String(facultyName || '').trim())
    .filter(Boolean)
    .map((facultyName) => ({
      faculty_name: facultyName,
      class_sections: (() => {
        const existing = findBestExistingClasses(facultyName);
        if (existing && existing.length) return existing;
        return facultyNames.filter((name) => String(name || '').trim()).length === 1 ? allowedClasses : [];
      })(),
    }));
}

function doClassSectionsMatchDepartment(classSections: string[], department: string) {
  const normalizedDepartment = String(department || '').trim().toUpperCase();
  if (!normalizedDepartment) return true;
  const sections = normalizeClassSections(classSections || []);
  if (!sections.length) return true;
  return sections.every((section) => section === normalizedDepartment || section.startsWith(`${normalizedDepartment} `));
}

function splitTestsBySemester<T extends { semester: string }>(tests: T[]) {
  return {
    sem1: tests.filter((test) => String(test.semester || '').trim() === '1'),
    sem2: tests.filter((test) => String(test.semester || '').trim() === '2'),
  };
}

function buildReportsOverviewCacheKey(department?: string, year?: number | null) {
  return JSON.stringify({
    department: String(department || '').trim().toUpperCase(),
    year: Number(year || 0) || 0,
  });
}

function buildDashboardOverviewCacheKey() {
  return 'dashboard-overview';
}

function buildUsersOverviewCacheKey() {
  return 'users-overview';
}

function buildCdpOverviewCacheKey(filters?: {
  department?: string;
  year?: number | null;
  semester?: string;
  subject_id?: number | null;
}) {
  return JSON.stringify({
    department: String(filters?.department || '').trim().toUpperCase(),
    year: Number(filters?.year || 0) || 0,
    semester: String(filters?.semester || '').trim(),
    subject_id: Number(filters?.subject_id || 0) || 0,
  });
}

function buildActivityOverviewCacheKey(filters?: {
  department?: string;
  year?: number | null;
  semester?: string;
  test_name?: string;
  q?: string;
  sort?: string;
}) {
  const normalizedSort = String(filters?.sort || '').trim() || 'pending_first';
  return JSON.stringify({
    department: String(filters?.department || '').trim().toUpperCase(),
    year: Number(filters?.year || 0) || 0,
    semester: String(filters?.semester || '').trim(),
    test_name: String(filters?.test_name || '').trim(),
    q: String(filters?.q || '').trim(),
    sort: normalizedSort,
  });
}

function buildActivityScopeSeedKey(payload: Pick<ActivityOverviewPayload, 'selectedDepartment' | 'selectedYear' | 'cacheMeta'>) {
  const department = String(payload.selectedDepartment || '').trim().toUpperCase();
  const year = Number(payload.selectedYear || 0) || 0;
  if (!department || !year) return '';
  return [
    department,
    year,
    String(payload.cacheMeta?.version || 0),
    String(payload.cacheMeta?.generatedAt || ''),
  ].join('::');
}

function stripActivityPrefetchedResults(payload: ActivityOverviewPayload): ActivityOverviewPayload {
  if (!payload.prefetchedResults?.length) return payload;
  return {
    ...payload,
    prefetchedResults: undefined,
  };
}

function shouldPersistActivityOverviewPayload(payload: ActivityOverviewPayload) {
  return !payload.prefetchedResults?.length
    && !String(payload.selectedSemester || '').trim()
    && !String(payload.selectedTestName || '').trim();
}

function buildActivityScopeReportCacheKey(filters?: {
  department?: string;
  year?: number | null;
  semester?: string;
  test_name?: string;
}) {
  return JSON.stringify({
    department: String(filters?.department || '').trim().toUpperCase(),
    year: Number(filters?.year || 0) || 0,
    semester: String(filters?.semester || '').trim(),
    test_name: String(filters?.test_name || '').trim(),
  });
}

function buildPersistentCacheNamespace(payload: BootstrapPayload | null) {
  const email = String(payload?.user?.email || '').trim().toLowerCase();
  const role = String(payload?.user?.role || '').trim().toLowerCase();
  if (!email || !role) return '';
  return [
    String(payload?.appVersion || 'app'),
    `rmv${Number(payload?.readModelVersion || 0) || 0}`,
    email,
    role,
  ].join('::');
}

function buildTestDetailMarksSnapshot(payload: TestDetailPayload | null) {
  const snapshot: Record<string, Record<string, string>> = {};
  if (!payload) return snapshot;
  for (const student of payload.students || []) {
    const regNo = String(student.reg_no || '').trim();
    if (!regNo) continue;
    snapshot[regNo] = Object.fromEntries(
      (payload.subjects || []).map((subject) => [
        subject,
        String(student.marks?.[subject] || '').trim(),
      ]),
    );
  }
  return snapshot;
}

function toBooleanString(value: string | undefined) {
  return String(value || '').trim().toLowerCase() === 'true';
}

function normalizeDesktopSendTargetPreference(value: string | undefined): DesktopSendTargetPreference {
  const candidate = String(value || '').trim().toLowerCase();
  if (candidate === 'chrome' || candidate === 'edge' || candidate === 'whatsapp_desktop') return candidate;
  return 'default_browser';
}

function isDesktopSendWorkspaceEnabled(config: BootstrapPayload['appConfig'] | null | undefined) {
  return runtimeConfig.isDesktop
    && String(config?.desktop_send_workspace_enabled || 'true').trim().toLowerCase() !== 'false';
}

function getDesktopSendTargetPreference(config: BootstrapPayload['appConfig'] | null | undefined): DesktopSendTargetPreference {
  return normalizeDesktopSendTargetPreference(config?.desktop_send_target_preference);
}

function getDesktopWorkspaceLaunchTarget(): DesktopSendTargetPreference {
  return 'whatsapp_desktop';
}

function getDesktopSendTargetLabel(preference: DesktopSendTargetPreference, availableTargets?: DesktopSendTargetAvailability) {
  if (preference === 'whatsapp_desktop' && availableTargets?.whatsapp_desktop) return 'WhatsApp Desktop';
  if (preference === 'chrome' && availableTargets?.chrome) return 'Google Chrome';
  if (preference === 'edge' && availableTargets?.edge) return 'Microsoft Edge';
  return 'Default Browser';
}

function resolveDesktopSendMode(_config: BootstrapPayload['appConfig'] | null | undefined): CounselorSendMode {
  return runtimeConfig.isDesktop ? 'app' : 'web';
}

async function resolveDesktopSendModeWithPresence(_config: BootstrapPayload['appConfig'] | null | undefined): Promise<CounselorSendMode> {
  if (!runtimeConfig.isDesktop) return 'web';
  try {
    const availability = await getAvailableDesktopSendTargets();
    return availability.whatsapp_desktop ? 'app' : 'web';
  } catch {
    return 'web';
  }
}

function resolveCounselorSendBackendMode(mode: CounselorSendMode): 'app' | 'web' {
  return mode === 'embed' ? 'web' : mode;
}

function formatDateTime(value: string | null | undefined) {
  const raw = String(value || '').trim();
  if (!raw) return '--';
  return raw.slice(0, 16).replace('T', ' ');
}

function buildNoticeAttachmentPreviewUrl(attachment: { public_token?: string; public_url?: string }) {
  const token = String(attachment?.public_token || '').trim();
  if (token) {
    const directServerUrl = String(resolveDirectServerUrl(`/api/notice-files/${token}`) || '').trim();
    if (directServerUrl) return directServerUrl;
  }
  return String(attachment?.public_url || '').trim() || (token ? `/api/notice-files/${token}` : '');
}

function formatUtcSqlDateTime(value: string | null | undefined) {
  const raw = String(value || '').trim();
  if (!raw) return '--';
  const normalized = raw.includes('T') ? raw : raw.replace(' ', 'T');
  const assumedUtc = /(?:Z|[+-]\d{2}:\d{2})$/i.test(normalized) ? normalized : `${normalized}Z`;
  const date = new Date(assumedUtc);
  if (Number.isNaN(date.getTime())) return formatDateTime(raw);
  return date.toLocaleString('en-GB', {
    day: '2-digit',
    month: 'short',
    year: 'numeric',
    hour: '2-digit',
    minute: '2-digit',
    hour12: false,
  }).replace(',', '');
}

function isSmtpConfigured(config: BootstrapPayload['appConfig'] | null | undefined) {
  return !!String(config?.smtp_server || '').trim()
    && !!String(config?.smtp_username || '').trim()
    && !!String(config?.smtp_password || '').trim();
}

function readSummaryMetric(marks: Record<string, string>, keys: string[]) {
  for (const key of keys) {
    if (marks[key] !== undefined && String(marks[key]).trim() !== '') {
      return marks[key];
    }
  }
  return '-';
}

function readSummaryMetricNumber(marks: Record<string, string>, keys: string[]) {
  const value = readSummaryMetric(marks, keys);
  const numeric = Number.parseFloat(String(value || '').replace(/[^0-9.-]/g, ''));
  return Number.isFinite(numeric) ? numeric : -1;
}

function isMobileUi() {
  const viewportMobile = typeof window !== 'undefined' && window.matchMedia?.(`(max-width: ${MOBILE_BREAKPOINT}px)`).matches;
  const uaMobile = typeof navigator !== 'undefined' && MOBILE_UA_RE.test(String(navigator.userAgent || ''));
  return !!viewportMobile || !!uaMobile;
}

function normalizeMetricKey(key: string) {
  return String(key || '').toLowerCase().replace(/[^a-z0-9]/g, '');
}

function convertWhatsAppAppLinkToWeb(waLink: string) {
  const raw = String(waLink || '').trim();
  if (!raw) return '';
  if (/^https:\/\/web\.whatsapp\.com\/send/i.test(raw)) return raw;
  if (/^whatsapp:\/\/send\?/i.test(raw)) {
    const query = raw.split('?')[1] || '';
    const params = new URLSearchParams(query);
    const phone = String(params.get('phone') || '').trim();
    const text = String(params.get('text') || '').trim();
    const webParams = new URLSearchParams();
    if (phone) webParams.set('phone', phone);
    if (text) webParams.set('text', text);
    webParams.set('type', 'phone_number');
    webParams.set('app_absent', '0');
    return `https://web.whatsapp.com/send/?${webParams.toString()}`;
  }
  return raw;
}

function convertWhatsAppWebLinkToApp(waLink: string) {
  const raw = String(waLink || '').trim();
  if (!raw) return '';
  if (/^whatsapp:\/\/send\?/i.test(raw)) return raw;
  if (/^https:\/\/wa\.me\//i.test(raw)) {
    try {
      const url = new URL(raw);
      const phone = String(url.pathname || '').replace(/^\/+/, '').replace(/\D/g, '').trim();
      const text = String(url.searchParams.get('text') || '').trim();
      const params = new URLSearchParams();
      if (phone) params.set('phone', phone);
      if (text) params.set('text', text);
      return phone ? `whatsapp://send?${params.toString()}` : raw;
    } catch {
      return raw;
    }
  }
  if (/^https:\/\/api\.whatsapp\.com\/send\/?/i.test(raw)) {
    try {
      const url = new URL(raw);
      const phone = String(url.searchParams.get('phone') || '').replace(/\D/g, '').trim();
      const text = String(url.searchParams.get('text') || '').trim();
      const params = new URLSearchParams();
      if (phone) params.set('phone', phone);
      if (text) params.set('text', text);
      return phone ? `whatsapp://send?${params.toString()}` : raw;
    } catch {
      return raw;
    }
  }
  if (/^https:\/\/web\.whatsapp\.com\/send\/?/i.test(raw)) {
    try {
      const url = new URL(raw);
      const phone = String(url.searchParams.get('phone') || '').trim();
      const text = String(url.searchParams.get('text') || '').trim();
      const params = new URLSearchParams();
      if (phone) params.set('phone', phone);
      if (text) params.set('text', text);
      return `whatsapp://send?${params.toString()}`;
    } catch {
      return raw;
    }
  }
  return raw;
}

function convertAnyWhatsAppLinkToAndroidApp(waLink: string) {
  const appLike = convertWhatsAppWebLinkToApp(waLink);
  if (/^whatsapp:\/\/send\?/i.test(appLike)) {
    const query = appLike.split('?')[1] || '';
    const params = new URLSearchParams(query);
    const phone = String(params.get('phone') || '').replace(/\D/g, '').trim();
    const text = String(params.get('text') || '').trim();
    if (!phone) return '';
    return text ? `https://wa.me/${phone}?text=${encodeURIComponent(text)}` : `https://wa.me/${phone}`;
  }
  return appLike;
}

function resolveWaLinkByMode(rawLink: string, mode: 'app' | 'web') {
  if (isMobileUi()) return convertAnyWhatsAppLinkToAndroidApp(rawLink);
  return mode === 'web' ? convertWhatsAppAppLinkToWeb(rawLink) : convertWhatsAppWebLinkToApp(rawLink);
}

const WHATSAPP_VERIFICATION_WEB_LINK = 'https://web.whatsapp.com/';

function openWhatsAppAppDirect(waLink: string) {
  const appLink = resolveWaLinkByMode(waLink, 'app');
  if (!appLink) return false;
  if (isMobileUi()) {
    openExternalLink(appLink);
    return true;
  }
  if (runtimeConfig.isDesktop) return openExternalLink(appLink);
  try {
    const iframe = document.createElement('iframe');
    iframe.style.display = 'none';
    iframe.setAttribute('aria-hidden', 'true');
    iframe.src = appLink;
    document.body.appendChild(iframe);
    window.setTimeout(() => iframe.remove(), 1200);
    return true;
  } catch {
    try {
      openExternalLink(appLink);
      return true;
    } catch {
      return false;
    }
  }
}

function openWhatsAppWebDirect(waLink: string) {
  const webLink = resolveWaLinkByMode(waLink, 'web');
  if (!webLink) return false;
  try {
    openExternalLink(webLink);
    return true;
  } catch {
    return false;
  }
}

function saveSendReturnState(state: SendReturnState) {
  try {
    sessionStorage.setItem(SEND_RETURN_STATE_KEY, JSON.stringify(state));
  } catch {
    // Ignore storage failures.
  }
}

function consumeSendReturnState() {
  try {
    const raw = sessionStorage.getItem(SEND_RETURN_STATE_KEY);
    if (!raw) return null;
    sessionStorage.removeItem(SEND_RETURN_STATE_KEY);
    const parsed = JSON.parse(raw) as Partial<SendReturnState>;
    if (
      !parsed
      || (parsed.kind !== 'report' && parsed.kind !== 'notice')
      || parsed.mode !== 'web'
      || !Number.isFinite(Number(parsed.id))
      || !Number.isFinite(Number(parsed.timestamp))
    ) {
      return null;
    }
    if (Date.now() - Number(parsed.timestamp) > SEND_RETURN_STATE_MAX_AGE_MS) {
      return null;
    }
    return {
      kind: parsed.kind,
      id: Number(parsed.id),
      mode: 'web' as const,
      timestamp: Number(parsed.timestamp),
    };
  } catch {
    return null;
  }
}

function collectSubjectsFromSendRows(rows: CounselorSendReportRow[]) {
  const seen = new Set<string>();
  const subjects: FieldOrderEntry[] = [];

  for (const row of rows || []) {
    for (const rawKey of Object.keys(row.marks || {})) {
      const normalized = normalizeMetricKey(rawKey);
      if (!normalized || IGNORED_KEYS.has(normalized)) continue;
      if (FAILED_KEYS.has(normalized) || NOT_ATTENDED_KEYS.has(normalized) || GPA_KEYS.has(normalized)) continue;
      if (String(rawKey || '').trim().toLowerCase().startsWith('unnamed')) continue;
      if (/^subject[_\s-]*\d+$/i.test(String(rawKey || '').trim())) continue;
      if (seen.has(normalized)) continue;
      seen.add(normalized);
      subjects.push({
        type: 'subject',
        label: String(rawKey).trim(),
        rawKey: String(rawKey).trim(),
        normalizedKey: normalized,
      });
    }
  }

  return subjects;
}

function buildDefaultOrderList(rows: CounselorSendReportRow[]): FieldOrderEntry[] {
  return [
    ...collectSubjectsFromSendRows(rows),
    { type: 'metric', metricKey: 'failed_subjects', label: 'Failed Subjects' },
    { type: 'metric', metricKey: 'not_attended', label: 'No of Subjects Absent' },
    { type: 'metric', metricKey: 'gpa', label: 'GPA' },
  ];
}

function buildNormalizedMarkMap(marks: Record<string, string>) {
  const normalizedToValue: Record<string, string> = {};
  for (const [rawKey, rawValue] of Object.entries(marks || {})) {
    normalizedToValue[normalizeMetricKey(rawKey)] = String(rawValue ?? '').trim();
  }
  return normalizedToValue;
}

function buildSubjectsTableFromOrder(orderEntries: FieldOrderEntry[], marks: Record<string, string>) {
  const normalizedToValue = buildNormalizedMarkMap(marks);
  const lines: string[] = [];

  for (const entry of orderEntries || []) {
    if (entry.type === 'subject') {
      let value = '';
      if (Object.prototype.hasOwnProperty.call(marks, entry.rawKey)) {
        value = String(marks[entry.rawKey] ?? '').trim();
      } else {
        const found = Object.entries(marks || {}).find(([key]) => normalizeMetricKey(key) === entry.normalizedKey);
        value = found ? String(found[1] ?? '').trim() : '';
      }
      if (value) lines.push(`${entry.label} : ${value}`.trim());
      continue;
    }

    const keySet =
      entry.metricKey === 'failed_subjects'
        ? FAILED_KEYS
        : entry.metricKey === 'not_attended'
          ? NOT_ATTENDED_KEYS
          : GPA_KEYS;
    const foundKey = Array.from(keySet).find((key) => normalizedToValue[key] !== undefined);
    const value = foundKey ? normalizedToValue[foundKey] : '';
    if (String(value || '').trim()) {
      lines.push(`${entry.label} : ${value}`.trim());
    }
  }

  return lines.join('\n').trim();
}

function applyReportTemplate(template: string, variables: Record<string, string>) {
  let output = String(template || '');
  for (const [key, value] of Object.entries(variables || {})) {
    output = output.split(`{${key}}`).join(String(value ?? ''));
  }
  return output;
}

export default function App() {
  const MIN_BOOT_LOADER_MS = 900;
  const [bootstrap, setBootstrap] = useState<BootstrapPayload | null>(null);
  const [bootLoading, setBootLoading] = useState(() => shouldUseBootLoaderOnInitialLoad());
  const [bootStatus, setBootStatus] = useState('Preparing workspace...');
  const [sessionEndNotice, setSessionEndNotice] = useState<BootstrapPayload['sessionEndNotice']>(null);
  const [activeTab, setActiveTab] = useState('reports');
  const [flash, setFlash] = useState<FlashState>(null);
  const [mobileSidebarOpen, setMobileSidebarOpen] = useState(false);
  const [loginState, setLoginState] = useState<LoginState>({
    identifier: '',
    password: '',
    otp_code: '',
    loading: false,
    error: '',
    conflict: null,
    conflictAuthMethod: null,
  });
  const [loginOtpState, setLoginOtpState] = useState<LoginOtpState | null>(null);
  const [loginRoleSelectionState, setLoginRoleSelectionState] = useState<LoginRoleSelectionState | null>(null);
  const [roleSwitchModalOpen, setRoleSwitchModalOpen] = useState(false);
  const [roleSwitchSelectedAccountEmail, setRoleSwitchSelectedAccountEmail] = useState('');
  const [roleSwitchLoading, setRoleSwitchLoading] = useState(false);
  const [roleSwitchError, setRoleSwitchError] = useState('');
  const [roleSwitchOptionsOverride, setRoleSwitchOptionsOverride] = useState<RoleSelectionOption[]>([]);
  const [forgotPasswordState, setForgotPasswordState] = useState<ForgotPasswordState>({
    open: false,
    stage: 'request',
    identifier: '',
    maskedEmail: '',
    otp_code: '',
    new_password: '',
    confirm_password: '',
    loading: false,
    error: '',
  });
  const [selfPasswordModalOpen, setSelfPasswordModalOpen] = useState(false);
  const [selfPasswordDraft, setSelfPasswordDraft] = useState<SelfPasswordDraft>({
    current_password: '',
    otp_code: '',
    new_password: '',
    confirm_password: '',
  });
  const [selfPasswordSaving, setSelfPasswordSaving] = useState(false);
  const [selfPasswordSendingOtp, setSelfPasswordSendingOtp] = useState(false);
  const [selfPasswordOtpSentTo, setSelfPasswordOtpSentTo] = useState('');
  const [showPassword, setShowPassword] = useState(false);
  const [users, setUsers] = useState<UserRecord[]>([]);
  const [usersLoading, setUsersLoading] = useState(false);
  const [userSearch, setUserSearch] = useState('');
  const deferredUserSearch = useDeferredValue(userSearch);
  const [userFilterTrayOpen, setUserFilterTrayOpen] = useState(false);
  const [userFilterDepartment, setUserFilterDepartment] = useState('');
  const [userFilterRole, setUserFilterRole] = useState('');
  const [userFilterStatus, setUserFilterStatus] = useState('');
  const [userFilterYear, setUserFilterYear] = useState('');
  const [userFilterStudentList, setUserFilterStudentList] = useState('');
  const [userSortBy, setUserSortBy] = useState('name_asc');
  const [userAssignableRoles, setUserAssignableRoles] = useState<Role[]>([]);
  const [userActorScopes, setUserActorScopes] = useState<ScopeRow[]>([]);
  const [userCreateForm, setUserCreateForm] = useState({
    name: '',
    email: '',
    password: '',
    confirm_password: '',
    role: 'counselor' as Role,
    designation: '',
    department: '',
    year_level: '1',
    max_students: '30',
    scope_pairs: [] as string[],
  });
  const [userSaving, setUserSaving] = useState(false);
  const userCreateDraftLoadedRef = useRef(false);
  const [userEditDraft, setUserEditDraft] = useState<{
    original_email: string;
    name: string;
    email: string;
    password: string;
    role: Role;
    designation: string;
    department: string;
    year_level: string;
    max_students: string;
    scope_pairs: string[];
  } | null>(null);
  const [userActionTarget, setUserActionTarget] = useState<{ kind: 'lock' | 'unlock' | 'delete'; user: UserRecord } | null>(null);
  const [userActionLoading, setUserActionLoading] = useState(false);
  const [linkedUserGroupEmail, setLinkedUserGroupEmail] = useState('');
  const [bulkCounselorForm, setBulkCounselorForm] = useState<{ year_level: string; file: File | null }>({ year_level: '1', file: null });
  const [bulkCounselorUploadKey, setBulkCounselorUploadKey] = useState(0);
  const [bulkCounselorSaving, setBulkCounselorSaving] = useState(false);
  const [studentListModalOpen, setStudentListModalOpen] = useState(false);
  const [studentListCounselor, setStudentListCounselor] = useState<UserRecord | null>(null);
  const [studentListRows, setStudentListRows] = useState<CounselorStudentRecord[]>([]);
  const [studentListLoading, setStudentListLoading] = useState(false);
  const [studentListSaving, setStudentListSaving] = useState(false);
  const [studentUploadKey, setStudentUploadKey] = useState(0);
  const [studentQuickAdd, setStudentQuickAdd] = useState({ reg_no: '', student_name: '', parent_phone: '', parent_email: '' });
  const [confirmDialog, setConfirmDialog] = useState<ConfirmDialogState | null>(null);
  const [templateDownloadsOpen, setTemplateDownloadsOpen] = useState(false);
  const [departments, setDepartments] = useState<DepartmentRecord[]>([]);
  const [departmentsLoading, setDepartmentsLoading] = useState(false);
  const [departmentForm, setDepartmentForm] = useState({ code: '', name: '' });
  const [departmentEdit, setDepartmentEdit] = useState<{ id: number; code: string; name: string } | null>(null);
  const [departmentActionState, setDepartmentActionState] = useState<DepartmentActionState>(null);
  const [departmentActionLoading, setDepartmentActionLoading] = useState(false);
  const [noticesLoading, setNoticesLoading] = useState(false);
  const [noticesData, setNoticesData] = useState<NoticesOverviewPayload | null>(null);
  const [noticeFilters, setNoticeFilters] = useState({
    department: '',
    year: '',
    status: '',
    date_from: '',
    date_to: '',
  });
  const [noticeForm, setNoticeForm] = useState({
    notice_id: 0,
    notice_title: '',
    notice_message_text: '',
    notice_send_to_all: false,
    scope_pairs: [] as string[],
    remove_attachment_ids: [] as number[],
    files: [] as File[],
  });
  const [savingNotice, setSavingNotice] = useState(false);
  const [noticeFileInputKey, setNoticeFileInputKey] = useState(0);
  const [selectedNoticeCompletion, setSelectedNoticeCompletion] = useState<NoticeCompletionRow | null>(null);
  const [counselorNoticeSendVerify, setCounselorNoticeSendVerify] = useState<CounselorNoticeSendVerifyState | null>(null);
  const [counselorNoticeSendLoading, setCounselorNoticeSendLoading] = useState(false);
  const [counselorNoticeSendPage, setCounselorNoticeSendPage] = useState<CounselorNoticeSendPagePayload | null>(null);
  const [counselorNoticeSendVars, setCounselorNoticeSendVars] = useState({
    title: '',
    text: '',
    template: '',
    sendMode: 'app' as CounselorSendMode,
  });
  const counselorNoticeSendVarsRef = useRef(counselorNoticeSendVars);
  const [counselorNoticeAutoTemplate, setCounselorNoticeAutoTemplate] = useState('');
  const [counselorNoticeTemplateEdited, setCounselorNoticeTemplateEdited] = useState(false);
  const [counselorNoticeBatchRunning, setCounselorNoticeBatchRunning] = useState(false);
  const [counselorNoticeBatchIndex, setCounselorNoticeBatchIndex] = useState(0);
  const [counselorNoticeBatchLastStudent, setCounselorNoticeBatchLastStudent] = useState('');
  const [counselorNoticeIncludeGenerated, setCounselorNoticeIncludeGenerated] = useState(false);
  const [reportsLoading, setReportsLoading] = useState(false);
  const [reportsData, setReportsData] = useState<ReportsOverviewPayload | null>(null);
  const [subjectsLoading, setSubjectsLoading] = useState(false);
  const [subjectsData, setSubjectsData] = useState<SubjectsOverviewPayload | null>(null);
  const [subjectForm, setSubjectForm] = useState({
    subject_code: '',
    subject_name: '',
    faculty_name: '',
    google_sheet_link: '',
    academic_start_year: String(getDefaultSubjectAttendanceYear()),
    academic_end_year: String(getDefaultSubjectAttendanceYear()),
    class_sections: [] as string[],
    faculty_allocations: [] as Array<{ faculty_name: string; class_sections: string[] }>,
  });
  const [subjectEditId, setSubjectEditId] = useState<number | null>(null);
  const [subjectSaving, setSubjectSaving] = useState(false);
  const [subjectParsing, setSubjectParsing] = useState(false);
  const [subjectLastParsedLink, setSubjectLastParsedLink] = useState('');
  const [subjectParsedClasses, setSubjectParsedClasses] = useState<string[]>([]);
  const [subjectParsedFaculties, setSubjectParsedFaculties] = useState<string[]>([]);
  const [subjectParseError, setSubjectParseError] = useState('');
  const subjectParseRequestRef = useRef(0);
  const reportsOverviewCacheRef = useRef(new Map<string, { timestamp: number; payload: ReportsOverviewPayload }>());
  const dashboardOverviewCacheRef = useRef(new Map<string, { timestamp: number; payload: DashboardOverviewPayload }>());
  const usersOverviewCacheRef = useRef(new Map<string, { timestamp: number; payload: UsersOverviewPayload }>());
  const subjectsOverviewCacheRef = useRef(new Map<string, { timestamp: number; payload: SubjectsOverviewPayload }>());
  const cdpOverviewCacheRef = useRef(new Map<string, { timestamp: number; payload: CdpOverviewPayload }>());
  const activityOverviewCacheRef = useRef(new Map<string, { timestamp: number; payload: ActivityOverviewPayload }>());
  const activityScopeReportCacheRef = useRef(new Map<string, { timestamp: number; payload: ActivityScopeReportPayload }>());
  const activityScopePrefetchRef = useRef(new Set<string>());
  const activityScopeSeededRef = useRef(new Set<string>());
  const tabWarmupKeyRef = useRef('');
  const [cdpLoading, setCdpLoading] = useState(false);
  const [cdpData, setCdpData] = useState<CdpOverviewPayload | null>(null);
  const [counselorOverviewLoading, setCounselorOverviewLoading] = useState(false);
  const [counselorOverview, setCounselorOverview] = useState<CounselorOverviewPayload | null>(null);
  const [counselorTestsLoading, setCounselorTestsLoading] = useState(false);
  const [counselorTests, setCounselorTests] = useState<CounselorVisibleTestRecord[]>([]);
  const [counselorMessagesLoading, setCounselorMessagesLoading] = useState(false);
  const [counselorMessages, setCounselorMessages] = useState<CounselorMessageRecord[]>([]);
  const [counselorMessageStats, setCounselorMessageStats] = useState<CounselorMessageStats | null>(null);
  const [counselorSendVerify, setCounselorSendVerify] = useState<CounselorSendVerifyState | null>(null);
  const [missingWhatsappPrompt, setMissingWhatsappPrompt] = useState<MissingWhatsappPromptState | null>(null);
  const [counselorSendLoading, setCounselorSendLoading] = useState(false);
  const [counselorSendPage, setCounselorSendPage] = useState<CounselorSendPagePayload | null>(null);
  const [desktopWhatsappState, setDesktopWhatsappState] = useState<DesktopEmbeddedWhatsappState>({
    supported: runtimeConfig.featureFlags.desktopSendWorkspaceSupported,
    active: false,
    loading: false,
    preferredTarget: 'default_browser',
    preferredTargetLabel: 'Default Browser',
    availableTargets: {
      default_browser: true,
      chrome: false,
      edge: false,
      whatsapp_desktop: false,
    },
    error: '',
  });
  const [desktopWhatsappWorkspaceReady, setDesktopWhatsappWorkspaceReady] = useState(false);
  const [desktopWhatsappWorkspaceStarted, setDesktopWhatsappWorkspaceStarted] = useState(false);
  const [desktopWhatsappWorkspaceBusy, setDesktopWhatsappWorkspaceBusy] = useState(false);
  const [desktopWhatsappWorkspaceTransition, setDesktopWhatsappWorkspaceTransition] = useState<null | 'enter' | 'exit'>(null);
  const [desktopWhatsappWorkspaceExiting, setDesktopWhatsappWorkspaceExiting] = useState(false);
  const [desktopWhatsappActiveTarget, setDesktopWhatsappActiveTarget] = useState<DesktopSendPendingTarget | null>(null);
  const [desktopWhatsappLoadingRow, setDesktopWhatsappLoadingRow] = useState<string | null>(null);
  const [desktopReportQueueState, setDesktopReportQueueState] = useState<Record<string, DesktopSendQueueState>>({});
  const [desktopNoticeQueueState, setDesktopNoticeQueueState] = useState<Record<string, DesktopSendQueueState>>({});
  const [desktopSettingsPanelOpen, setDesktopSettingsPanelOpen] = useState(false);
  const [notificationCenterOpen, setNotificationCenterOpen] = useState(false);
  const [loginNotificationPrompt, setLoginNotificationPrompt] = useState<AppNotificationItem | null>(null);
  const [notificationSeenVersion, setNotificationSeenVersion] = useState(0);
  const [notificationDeletedVersion, setNotificationDeletedVersion] = useState(0);
  const [serverNotificationState, setServerNotificationState] = useState<{ readKeys: string[]; deletedKeys: string[] }>({ readKeys: [], deletedKeys: [] });
  const [configDesktopMode, setConfigDesktopMode] = useState<'server' | 'desktop'>('server');
  const [sendResultOpeningId, setSendResultOpeningId] = useState<number | null>(null);
  const [sendNoticeOpeningId, setSendNoticeOpeningId] = useState<number | null>(null);
  const [desktopAppSettings, setDesktopAppSettings] = useState<DesktopAppSettings | null>(null);
  const [desktopConnectivity, setDesktopConnectivity] = useState<DesktopConnectivityState | null>(null);
  const [desktopUpdateInfo, setDesktopUpdateInfo] = useState<DesktopUpdateInfo | null>(null);
  const [desktopSettingsSaving, setDesktopSettingsSaving] = useState(false);
  const [desktopUpdateChecking, setDesktopUpdateChecking] = useState(false);
  const [counselorSendVars, setCounselorSendVars] = useState({
    test_name: '',
    semester: '',
    batch_name: '',
    template: DEFAULT_REPORT_TEMPLATE,
    sendMode: 'app' as CounselorSendMode,
  });
  const counselorSendVarsRef = useRef(counselorSendVars);
  const [counselorFieldOrder, setCounselorFieldOrder] = useState<FieldOrderEntry[]>([]);
  const [counselorDefaultFieldOrder, setCounselorDefaultFieldOrder] = useState<FieldOrderEntry[]>([]);
  const [counselorBatchRunning, setCounselorBatchRunning] = useState(false);
  const [counselorBatchIndex, setCounselorBatchIndex] = useState(0);
  const [counselorBatchLastStudent, setCounselorBatchLastStudent] = useState('');
  const [counselorIncludeGenerated, setCounselorIncludeGenerated] = useState(false);
  const [testDetailLoading, setTestDetailLoading] = useState(false);
  const [testDetail, setTestDetail] = useState<TestDetailPayload | null>(null);
  const [testDetailSearch, setTestDetailSearch] = useState('');
  const [testDetailSort, setTestDetailSort] = useState('reg_asc');
  const testDetailOriginalMarksRef = useRef<Record<string, Record<string, string>>>({});
  const [testMetaDraft, setTestMetaDraft] = useState({ test_name: '', semester: '', batch_name: '', section: '' });
  const [savingMeta, setSavingMeta] = useState(false);
  const [savingMarks, setSavingMarks] = useState(false);
  const [uploadingReport, setUploadingReport] = useState(false);
  const [reportUploadInputKey, setReportUploadInputKey] = useState(0);
  const reportUploadScopeKeyRef = useRef('');
  const [reportUploadDraft, setReportUploadDraft] = useState({
    test_name: '',
    semester: '1',
    batch_name: '',
    section: '',
    upload_mode: 'new',
    file: null as File | null,
  });
  const [dashboardLoading, setDashboardLoading] = useState(false);
  const [dashboardData, setDashboardData] = useState<DashboardOverviewPayload | null>(null);
  const [activityLoading, setActivityLoading] = useState(false);
  const [activityData, setActivityData] = useState<ActivityOverviewPayload | null>(null);
  const [activityCopying, setActivityCopying] = useState(false);
  const [activityPdfLoading, setActivityPdfLoading] = useState(false);
  const [activityFilters, setActivityFilters] = useState({
    department: '',
    year: '',
    semester: '',
    test_name: '',
    q: '',
    sort: 'pending_first',
  });
  const deferredActivitySearch = useDeferredValue(activityFilters.q);
  const [adminMessagesLoading, setAdminMessagesLoading] = useState(false);
  const [adminMessagesData, setAdminMessagesData] = useState<AdminMessagesOverviewPayload | null>(null);
  const [adminMessageFilters, setAdminMessageFilters] = useState({
    day: '',
    q: '',
    year: '',
    month: '',
    day_num: '',
  });
  const [adminMessageSearch, setAdminMessageSearch] = useState('');
  const [adminMessagesLimit, setAdminMessagesLimit] = useState(DEFAULT_ADMIN_MESSAGES_LIMIT);
  const [selectedAdminMessageIds, setSelectedAdminMessageIds] = useState<number[]>([]);
  const [noticeCompletionSearch, setNoticeCompletionSearch] = useState('');
  const [noticeCompletionDepartment, setNoticeCompletionDepartment] = useState('');
  const [noticeCompletionYear, setNoticeCompletionYear] = useState('');
  const [noticeCompletionSort, setNoticeCompletionSort] = useState('pending_desc');
  const [noticeCompletionSortOpen, setNoticeCompletionSortOpen] = useState(false);
  const [noticeRecordSearch, setNoticeRecordSearch] = useState('');
  const [noticeRecordSort, setNoticeRecordSort] = useState('latest');
  const [noticeRecordSortOpen, setNoticeRecordSortOpen] = useState(false);
  const [monitoringLoading, setMonitoringLoading] = useState(false);
  const [monitoringData, setMonitoringData] = useState<MonitoringOverviewPayload | null>(null);
  const [monitoringSearch, setMonitoringSearch] = useState('');
  const deferredMonitoringSearch = useDeferredValue(monitoringSearch);
  const [monitoringStatusFilter, setMonitoringStatusFilter] = useState('all');
  const [monitoringAuthFilter, setMonitoringAuthFilter] = useState('all');
  const [monitoringSortBy, setMonitoringSortBy] = useState('last_activity_desc');
  const [databaseLoading, setDatabaseLoading] = useState(false);
  const [databaseData, setDatabaseData] = useState<DatabaseOverviewPayload | null>(null);
  const [databaseBatchName, setDatabaseBatchName] = useState('');
  const [databaseOverwrite, setDatabaseOverwrite] = useState(false);
  const [databaseBackupCreating, setDatabaseBackupCreating] = useState(false);
  const [databaseBackupAction, setDatabaseBackupAction] = useState<BackupActionState>(null);
  const [databaseActionPassword, setDatabaseActionPassword] = useState('');
  const [databaseActionLoading, setDatabaseActionLoading] = useState(false);
  const [archiveYearStart, setArchiveYearStart] = useState('');
  const [archiveYearEnd, setArchiveYearEnd] = useState('');
  const [archiveYearOverwrite, setArchiveYearOverwrite] = useState(false);
  const [databaseProgress, setDatabaseProgress] = useState<DatabaseProgressState>(null);
  const [configLoading, setConfigLoading] = useState(false);
  const [configData, setConfigData] = useState<ConfigOverviewPayload | null>(null);
  const [configForm, setConfigForm] = useState<Record<string, string | boolean>>({});
  const [configBaselineSnapshot, setConfigBaselineSnapshot] = useState('');
  const [configPasswordPrompt, setConfigPasswordPrompt] = useState<ConfigPasswordPromptState>(null);
  const [configPromptPassword, setConfigPromptPassword] = useState('');
  const [pendingConfigTab, setPendingConfigTab] = useState<string | null>(null);
  const [envDraft, setEnvDraft] = useState('');
  const [configSaving, setConfigSaving] = useState(false);
  const [envSaving, setEnvSaving] = useState(false);
  const [smtpTesting, setSmtpTesting] = useState(false);
  const [resetPasswordDraft, setResetPasswordDraft] = useState({
    target_email: '',
    new_password: '',
    confirm_password: '',
    force_logout: true,
  });
  const [resetUserSearch, setResetUserSearch] = useState('');
  const deferredResetUserSearch = useDeferredValue(resetUserSearch);
  const [resetUserDepartmentFilter, setResetUserDepartmentFilter] = useState('');
  const [resetUserYearFilter, setResetUserYearFilter] = useState('');
  const [previewUserSearch, setPreviewUserSearch] = useState('');
  const [previewUserEmail, setPreviewUserEmail] = useState('');
  const [loginConflictInfoOpen, setLoginConflictInfoOpen] = useState(false);
  const [resetSaving, setResetSaving] = useState(false);
  const [serverConsoleLoading, setServerConsoleLoading] = useState(false);
  const [serverConsoleData, setServerConsoleData] = useState<ServerConsolePayload | null>(null);
  const [configImporting, setConfigImporting] = useState(false);
  const [theme, setTheme] = useState<'light' | 'dark'>(() => {
    try {
      return (localStorage.getItem('theme') as 'light' | 'dark') || 'light';
    } catch {
      return 'light';
    }
  });
  const counselorBatchTimerRef = useRef<number | null>(null);
  const counselorBatchQueueRef = useRef<CounselorSendReportRow[]>([]);
  const counselorBatchIndexRef = useRef(0);
  const archiveYearLabel = useMemo(
    () => buildAcademicYearLabel(archiveYearStart, archiveYearEnd),
    [archiveYearStart, archiveYearEnd],
  );
  const archiveViewActive = Boolean(bootstrap?.archiveView?.active);
  const counselorBatchRunningRef = useRef(false);
  const counselorNoticeBatchTimerRef = useRef<number | null>(null);
  const noticeComposerRef = useRef<HTMLDivElement | null>(null);
  const desktopReportWorkspaceRef = useRef<HTMLDivElement | null>(null);
  const desktopNoticeWorkspaceRef = useRef<HTMLDivElement | null>(null);
  const desktopReportQueueShellRef = useRef<HTMLDivElement | null>(null);
  const desktopNoticeQueueShellRef = useRef<HTMLDivElement | null>(null);
  const confirmResolverRef = useRef<((value: boolean) => void) | null>(null);
  const counselorNoticeBatchQueueRef = useRef<CounselorSendNoticeRow[]>([]);
  const counselorNoticeBatchIndexRef = useRef(0);
  const counselorNoticeBatchRunningRef = useRef(false);
  const counselorSendReturnRestoreRef = useRef(false);
  const configImportInputRef = useRef<HTMLInputElement | null>(null);
  const bootLoaderShownAtRef = useRef(typeof performance !== 'undefined' ? performance.now() : Date.now());
  const mainContentRef = useRef<HTMLElement | null>(null);
  const contentAreaRef = useRef<HTMLDivElement | null>(null);

  function readOverviewCacheEntry<T>(
    ref: MutableRefObject<Map<string, { timestamp: number; payload: T }>>,
    bucket: string,
    key: string,
  ) {
    const inMemory = ref.current.get(key);
    if (inMemory) return inMemory;
    const persisted = readPersistentCacheEntry<T>(persistentCacheNamespace, bucket, key);
    if (persisted) {
      ref.current.set(key, persisted);
      return persisted;
    }
    return null;
  }

  function writeOverviewCacheEntry<T>(
    ref: MutableRefObject<Map<string, { timestamp: number; payload: T }>>,
    bucket: string,
    key: string,
    payload: T,
    persist = true,
  ) {
    const entry = { timestamp: Date.now(), payload };
    ref.current.set(key, entry);
    if (persist) {
      writePersistentCacheEntry(persistentCacheNamespace, bucket, key, entry);
    }
    return entry;
  }

  function clearOverviewCacheBucket<T>(
    ref: MutableRefObject<Map<string, { timestamp: number; payload: T }>>,
    bucket: string,
  ) {
    ref.current.clear();
    clearPersistentCacheBucket(persistentCacheNamespace, bucket);
  }

  function invalidateOverviewCaches(buckets: Array<'dashboard' | 'reports' | 'users' | 'cdp' | 'activity' | 'activity-scope'>) {
    for (const bucket of buckets) {
      if (bucket === 'dashboard') {
        clearOverviewCacheBucket(dashboardOverviewCacheRef, 'dashboard');
        continue;
      }
      if (bucket === 'reports') {
        clearOverviewCacheBucket(reportsOverviewCacheRef, 'reports');
        continue;
      }
      if (bucket === 'users') {
        clearOverviewCacheBucket(usersOverviewCacheRef, 'users');
        continue;
      }
      if (bucket === 'cdp') {
        clearOverviewCacheBucket(cdpOverviewCacheRef, 'cdp');
        continue;
      }
      if (bucket === 'activity') {
        clearOverviewCacheBucket(activityOverviewCacheRef, 'activity');
        continue;
      }
      if (bucket === 'activity-scope') {
        activityScopeReportCacheRef.current.clear();
      }
    }
  }

  function seedBootstrapOverviewCaches(payload: BootstrapPayload) {
    const namespace = buildPersistentCacheNamespace(payload);
    if (!namespace || !payload.prefetched) return;

    const now = Date.now();
    const seeds: Array<{ bucket: string; key: string; entry: { timestamp: number; payload: unknown } }> = [];

    if (payload.prefetched.dashboard) {
      const key = buildDashboardOverviewCacheKey();
      const entry = { timestamp: now, payload: payload.prefetched.dashboard };
      dashboardOverviewCacheRef.current.set(key, entry);
      seeds.push({ bucket: 'dashboard', key, entry });
    }
    if (payload.prefetched.reports) {
      const key = buildReportsOverviewCacheKey(
        payload.prefetched.reports.selectedDepartment,
        payload.prefetched.reports.selectedYear,
      );
      const entry = { timestamp: now, payload: payload.prefetched.reports };
      reportsOverviewCacheRef.current.set(key, entry);
      seeds.push({ bucket: 'reports', key, entry });
      if (key !== buildReportsOverviewCacheKey()) {
        reportsOverviewCacheRef.current.set(buildReportsOverviewCacheKey(), entry);
        seeds.push({ bucket: 'reports', key: buildReportsOverviewCacheKey(), entry });
      }
    }
    if (payload.prefetched.activity) {
      const key = buildActivityOverviewCacheKey({
        department: payload.prefetched.activity.selectedDepartment,
        year: payload.prefetched.activity.selectedYear,
        semester: payload.prefetched.activity.selectedSemester,
        test_name: payload.prefetched.activity.selectedTestName,
        q: payload.prefetched.activity.searchQuery,
        sort: payload.prefetched.activity.sortMode,
      });
      const entry = { timestamp: now, payload: payload.prefetched.activity };
      activityOverviewCacheRef.current.set(key, entry);
      if (shouldPersistActivityOverviewPayload(payload.prefetched.activity)) {
        seeds.push({ bucket: 'activity', key, entry });
      }
      if (key !== buildActivityOverviewCacheKey()) {
        activityOverviewCacheRef.current.set(buildActivityOverviewCacheKey(), entry);
        if (shouldPersistActivityOverviewPayload(payload.prefetched.activity)) {
          seeds.push({ bucket: 'activity', key: buildActivityOverviewCacheKey(), entry });
        }
      }
    }
    if (payload.prefetched.cdp) {
      const key = buildCdpOverviewCacheKey({
        department: payload.prefetched.cdp.selectedDepartment,
        year: payload.prefetched.cdp.selectedYear,
        semester: payload.prefetched.cdp.selectedSemester,
        subject_id: payload.prefetched.cdp.selectedSubjectId,
      });
      const entry = { timestamp: now, payload: payload.prefetched.cdp };
      cdpOverviewCacheRef.current.set(key, entry);
      seeds.push({ bucket: 'cdp', key, entry });
      if (key !== buildCdpOverviewCacheKey()) {
        cdpOverviewCacheRef.current.set(buildCdpOverviewCacheKey(), entry);
        seeds.push({ bucket: 'cdp', key: buildCdpOverviewCacheKey(), entry });
      }
    }

    seedPersistentCacheEntries(namespace, 'dashboard', seeds.filter((item) => item.bucket === 'dashboard').map((item) => ({ key: item.key, entry: item.entry })));
    seedPersistentCacheEntries(namespace, 'reports', seeds.filter((item) => item.bucket === 'reports').map((item) => ({ key: item.key, entry: item.entry })));
    seedPersistentCacheEntries(namespace, 'activity', seeds.filter((item) => item.bucket === 'activity').map((item) => ({ key: item.key, entry: item.entry })));
    seedPersistentCacheEntries(namespace, 'cdp', seeds.filter((item) => item.bucket === 'cdp').map((item) => ({ key: item.key, entry: item.entry })));
  }

  useEffect(() => {
    applyTheme(theme);
    try {
      localStorage.setItem('theme', theme);
    } catch {
      // Ignore storage failures.
    }
  }, [theme]);

  useEffect(() => {
    document.documentElement.classList.toggle('mobile-sidebar-open', mobileSidebarOpen);
    document.body.classList.toggle('mobile-sidebar-open', mobileSidebarOpen);
    return () => {
      document.documentElement.classList.remove('mobile-sidebar-open');
      document.body.classList.remove('mobile-sidebar-open');
    };
  }, [mobileSidebarOpen]);

  useEffect(() => {
    if (activeTab !== 'config' || !configData || JSON.stringify(configForm) === configBaselineSnapshot) return undefined;
    const handleBeforeUnload = (event: BeforeUnloadEvent) => {
      event.preventDefault();
      event.returnValue = '';
    };
    window.addEventListener('beforeunload', handleBeforeUnload);
    return () => window.removeEventListener('beforeunload', handleBeforeUnload);
  }, [activeTab, configBaselineSnapshot, configData, configForm]);

  async function warmInitialUiCaches(payload: BootstrapPayload, preferredTab?: string) {
    const viewer = payload.user;
    if (!viewer || !['admin', 'principal', 'hod', 'deo'].includes(viewer.role)) return null;

    const warmed: {
      reports?: ReportsOverviewPayload;
      dashboard?: DashboardOverviewPayload;
      activity?: ActivityOverviewPayload;
      cdp?: CdpOverviewPayload;
    } = {};

    if (payload.prefetched?.reports) {
      warmed.reports = payload.prefetched.reports;
    }
    if (payload.prefetched?.dashboard) {
      warmed.dashboard = payload.prefetched.dashboard;
    }
    if (payload.prefetched?.activity) {
      warmed.activity = payload.prefetched.activity;
    }
    if (payload.prefetched?.cdp) {
      warmed.cdp = payload.prefetched.cdp;
    }

    const defaultTab = preferredTab || payload.defaultTab || getDefaultTab(viewer);
    if (defaultTab === 'dashboard' && ['admin', 'principal', 'hod'].includes(viewer.role) && !warmed.dashboard) {
      setBootStatus('Preparing dashboard...');
      const dashboardPayload = await getDashboardOverview();
      warmed.dashboard = dashboardPayload;
      writeOverviewCacheEntry(dashboardOverviewCacheRef, 'dashboard', buildDashboardOverviewCacheKey(), dashboardPayload);
    } else if (defaultTab === 'activity' && !warmed.activity) {
      setBootStatus('Warming activity...');
      const activityPayload = await getActivityOverview();
      warmed.activity = activityPayload;
      writeOverviewCacheEntry(
        activityOverviewCacheRef,
        'activity',
        buildActivityOverviewCacheKey(),
        activityPayload,
        shouldPersistActivityOverviewPayload(activityPayload),
      );
    } else if (defaultTab === 'cdp' && !warmed.cdp) {
      setBootStatus('Warming CDP...');
      const cdpPayload = await getCdpOverview();
      warmed.cdp = cdpPayload;
      writeOverviewCacheEntry(cdpOverviewCacheRef, 'cdp', buildCdpOverviewCacheKey(), cdpPayload);
    } else if (defaultTab === 'reports' && !warmed.reports) {
      setBootStatus('Caching reports...');
      const reportsPayload = await getReportsOverview();
      warmed.reports = reportsPayload;
      writeOverviewCacheEntry(reportsOverviewCacheRef, 'reports', buildReportsOverviewCacheKey(), reportsPayload);
    }

    return warmed;
  }

  async function prefetchActivityScopeCombos(payload: ActivityOverviewPayload) {
    const department = String(payload.selectedDepartment || '').trim().toUpperCase();
    const year = Number(payload.selectedYear || 0) || 0;
    if (!department || !year) return;

    const scopeKey = `${department}::${year}`;
    if (activityScopePrefetchRef.current.has(scopeKey)) return;
    activityScopePrefetchRef.current.add(scopeKey);

    try {
      const prefetched = await prefetchActivityScope({ department, year });
      for (const entry of prefetched.entries || []) {
        const cacheKey = buildActivityOverviewCacheKey({
          department: entry.selectedDepartment,
          year: entry.selectedYear,
          semester: entry.selectedSemester,
          test_name: entry.selectedTestName,
          q: entry.searchQuery,
          sort: entry.sortMode,
        });
        writeOverviewCacheEntry(activityOverviewCacheRef, 'activity', cacheKey, entry, false);
      }
    } catch {
      activityScopePrefetchRef.current.delete(scopeKey);
    }
  }

  async function getCachedActivityScopeReport(filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
  }) {
    const cacheKey = buildActivityScopeReportCacheKey(filters);
    const cached = activityScopeReportCacheRef.current.get(cacheKey);
    if (cached && Date.now() - cached.timestamp < SCOPE_CACHE_TTL_MS) {
      return cached.payload;
    }
    const payload = await getActivityScopeReport(filters);
    activityScopeReportCacheRef.current.set(cacheKey, { timestamp: Date.now(), payload });
    return payload;
  }

  async function warmActivityScopeReport(filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
  }) {
    try {
      await getCachedActivityScopeReport(filters);
    } catch {
      // Ignore background prefetch failures.
    }
  }

  async function waitForNextPaint() {
    await new Promise<void>((resolve) => {
      window.requestAnimationFrame(() => {
        window.requestAnimationFrame(() => resolve());
      });
    });
  }

  async function waitForMinimumBootLoaderTime() {
    const now = typeof performance !== 'undefined' ? performance.now() : Date.now();
    const remaining = Math.max(0, MIN_BOOT_LOADER_MS - (now - bootLoaderShownAtRef.current));
    if (!remaining) return;
    await new Promise<void>((resolve) => window.setTimeout(resolve, remaining));
  }

  useEffect(() => {
    void (async () => {
      const showBootLoader = shouldUseBootLoaderOnInitialLoad();
      try {
        await refreshBootstrap({ showBootLoader, forceDefaultTab: true });
      } finally {
        setBootLoading(false);
      }
    })();
  }, []);

  useEffect(() => {
    const params = new URLSearchParams(window.location.search);
    const auth = params.get('auth');
    if (auth !== 'google') return;

    const error = params.get('error');
    const errorDescription = params.get('error_description');
    const allowedDomain = params.get('allowed_domain');
    const success = params.get('success');
    const conflict = params.get('conflict');
    const roleSelect = params.get('role_select');

    if (roleSelect === '1') {
      void (async () => {
        try {
          const result = await getLoginRoleSelection();
          setLoginRoleSelectionState({
            authMethod: result.authMethod,
            loginEmail: result.loginEmail,
            options: result.options.map((option) => ({
              ...option,
              role: option.role as Role,
            })),
            selectedAccountEmail: String(result.options[0]?.accountEmail || ''),
          });
          setLoginState((prev) => ({ ...prev, loading: false, error: '', conflict: null, conflictAuthMethod: null, otp_code: '' }));
        } catch (selectionError) {
          setFlash({ type: 'error', message: selectionError instanceof Error ? selectionError.message : 'Role selection expired. Please sign in again.' });
        }
      })();
    } else if (success === '1') {
      setLoginState((prev) => ({ ...prev, loading: false, error: '', conflict: null, conflictAuthMethod: null, otp_code: '' }));
      setLoginConflictInfoOpen(false);
      setForgotPasswordState((prev) => ({ ...prev, loading: false, error: '' }));
      setFlash({ type: 'success', message: 'Google sign-in completed successfully.' });
      void refreshBootstrap({ showBootLoader: true, forceDefaultTab: true });
    } else if (conflict === '1') {
      const nextConflict = {
        browser: String(params.get('browser') || 'Unknown'),
        device_type: String(params.get('device_type') || 'Unknown'),
        ip_address: String(params.get('ip_address') || 'Unknown'),
        login_time: String(params.get('login_time') || ''),
      };
      clearRememberedAuthState();
      setLoginState((prev) => ({
        ...prev,
        loading: false,
        error: '',
        otp_code: '',
        conflictAuthMethod: 'google',
        conflict: nextConflict,
      }));
      setLoginConflictInfoOpen(loginConflictHasUnknownDetails(nextConflict));
      setForgotPasswordState((prev) => ({ ...prev, loading: false, error: '' }));
    } else if (error) {
      let message = 'Google sign-in could not be completed.';
      if (error === 'google_disabled') message = 'Google sign-in is not enabled right now.';
      else if (error === 'state_mismatch') message = 'Google sign-in state validation failed. Please try again.';
      else if (error === 'missing_code') message = 'Google sign-in did not return an authorization code.';
      else if (error === 'token_exchange_failed') message = 'Google sign-in token exchange failed.';
      else if (error === 'invalid_google_profile') message = 'Google sign-in did not return a valid verified email.';
      else if (error === 'invalid_domain') message = allowedDomain ? `Only ${allowedDomain} Google accounts are allowed.` : 'This Google account is not allowed.';
      else if (error === 'user_not_linked') message = 'Account not registered.';
      else if (error === 'account_in_test_mode') message = 'This account is currently being reviewed in admin test mode. Please try again after the admin exits test mode.';
      else if (error === 'access_denied') message = errorDescription || 'Google account access is blocked.';
      else if (errorDescription) message = errorDescription;
      clearRememberedAuthState();
      setLoginConflictInfoOpen(false);
      setFlash({ type: 'error', message });
    }

    params.delete('auth');
    params.delete('error');
    params.delete('error_description');
    params.delete('allowed_domain');
    params.delete('success');
    params.delete('conflict');
    params.delete('role_select');
    params.delete('browser');
    params.delete('device_type');
    params.delete('ip_address');
    params.delete('login_time');
    const nextQuery = params.toString();
    const nextUrl = `${window.location.pathname}${nextQuery ? `?${nextQuery}` : ''}${window.location.hash}`;
    window.history.replaceState({}, document.title, nextUrl);
  }, []);

  useEffect(() => {
    applyThemeColors(bootstrap?.appConfig || null);
  }, [bootstrap]);

  useEffect(() => {
    if (!flash) return;
    const timer = window.setTimeout(() => setFlash(null), 5000);
    return () => window.clearTimeout(timer);
  }, [flash]);

  useEffect(() => {
    if (!testDetail) {
      setTestDetailSearch('');
      setTestDetailSort('reg_asc');
      return;
    }
    setTestDetailSearch('');
    setTestDetailSort('reg_asc');
  }, [testDetail?.testId]);

  useEffect(() => {
    if (!reportsData?.selectedDepartment || !reportsData.selectedYear) return;
    const nextScopeKey = `${String(reportsData.selectedDepartment || '').trim().toUpperCase()}::${Number(reportsData.selectedYear || 0) || 0}`;
    const scopeChanged = Boolean(reportUploadScopeKeyRef.current) && reportUploadScopeKeyRef.current !== nextScopeKey;
    reportUploadScopeKeyRef.current = nextScopeKey;
    const nextBatchName = getDefaultBatchNameForYearLevel(reportsData.selectedYear, bootstrap?.appConfig || null);
    setReportUploadDraft((prev) => {
      return {
        ...prev,
        semester: prev.semester || '1',
        batch_name: prev.batch_name || nextBatchName,
        section: '',
        upload_mode: scopeChanged ? 'new' : prev.upload_mode,
        file: scopeChanged ? null : prev.file,
      };
    });
    if (scopeChanged) {
      setReportUploadInputKey((value) => value + 1);
    }
  }, [reportsData?.selectedDepartment, reportsData?.selectedYear, bootstrap?.appConfig]);

  useEffect(() => {
    const viewer = bootstrap?.user;
    if (!viewer || activeTab !== 'messages') return;
    if (!['admin', 'hod', 'deo'].includes(viewer.role)) return;
    const timer = window.setTimeout(() => {
      void reloadAdminMessages({
        day: adminMessageFilters.day || '',
        q: adminMessageSearch.trim(),
        year: adminMessageFilters.year || '',
        month: adminMessageFilters.month || '',
        day_num: adminMessageFilters.day_num || '',
      });
    }, 220);
    return () => window.clearTimeout(timer);
  }, [activeTab, adminMessageFilters.day, adminMessageFilters.day_num, adminMessageFilters.month, adminMessageFilters.year, adminMessageSearch, bootstrap?.user]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    const heartbeatSeconds = Math.max(10, Number(bootstrap.appConfig.session_heartbeat_interval || 30) || 30);
    const timer = window.setInterval(() => {
      void sendSessionHeartbeat().catch(() => undefined);
    }, heartbeatSeconds * 1000);
    return () => window.clearInterval(timer);
  }, [bootstrap?.user?.email, bootstrap?.appConfig.session_heartbeat_interval]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    const rafId = window.requestAnimationFrame(() => {
      if (document.activeElement instanceof HTMLElement && document.activeElement !== document.body) {
        document.activeElement.blur();
      }
      contentAreaRef.current?.scrollTo({ top: 0, left: 0, behavior: 'auto' });
      mainContentRef.current?.scrollTo({ top: 0, left: 0, behavior: 'auto' });
      window.scrollTo({ top: 0, left: 0, behavior: 'auto' });
    });
    return () => window.cancelAnimationFrame(rafId);
  }, [activeTab, bootstrap?.user?.email]);

  useEffect(() => {
    if (!bootstrap?.user || activeTab !== 'notices') return;
    if (counselorNoticeSendPage || counselorNoticeSendVerify) return;
    const timer = window.setTimeout(() => {
      void loadNotices({
        department: noticeFilters.department || undefined,
        year: noticeFilters.year ? Number(noticeFilters.year) : null,
        status: noticeFilters.status || undefined,
        date_from: noticeFilters.date_from || undefined,
        date_to: noticeFilters.date_to || undefined,
      });
    }, 220);
    return () => window.clearTimeout(timer);
  }, [
    activeTab,
    counselorNoticeSendPage,
    counselorNoticeSendVerify,
    bootstrap?.user,
    noticeFilters.date_from,
    noticeFilters.date_to,
    noticeFilters.department,
    noticeFilters.status,
    noticeFilters.year,
  ]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'users') return;
    if (!['admin', 'principal', 'deo'].includes(bootstrap.user.role)) return;
    void refreshUsersOverview();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'departments') return;
    if (!['admin', 'principal'].includes(bootstrap.user.role)) return;

    setDepartmentsLoading(true);
    void getDepartments()
      .then((payload) => setDepartments(payload.departments))
      .finally(() => setDepartmentsLoading(false));
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'notices') return;
    void loadNotices();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'reports') return;
    if (!['admin', 'principal', 'hod', 'deo'].includes(bootstrap.user.role)) return;
    void loadReports();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'subjects') return;
    if (!['admin', 'deo'].includes(bootstrap.user.role)) return;
    void loadSubjects();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'dashboard') return;
    if (!['admin', 'principal', 'hod'].includes(bootstrap.user.role)) return;
    void loadDashboardOverview();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    setAdminMessagesData(null);
    setAdminMessagesLimit(DEFAULT_ADMIN_MESSAGES_LIMIT);
    setAdminMessageFilters({
      day: '',
      q: '',
      year: '',
      month: '',
      day_num: '',
    });
    setSelectedAdminMessageIds([]);
  }, [bootstrap?.user?.email]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'activity') return;
    if (!['admin', 'principal', 'hod', 'deo'].includes(bootstrap.user.role)) return;
    void loadActivityOverview();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!activityData?.showYearPicker) return;
    const department = String(activityData.selectedDepartment || '').trim().toUpperCase();
    if (!department) return;
    for (const year of activityData.availableYears || []) {
      const scopeKey = `${department}::${year}`;
      if (activityScopePrefetchRef.current.has(scopeKey)) continue;
      activityScopePrefetchRef.current.add(scopeKey);
      void prefetchActivityScope({ department, year })
        .then((prefetched) => {
          for (const entry of prefetched.entries || []) {
            const cacheKey = buildActivityOverviewCacheKey({
              department: entry.selectedDepartment,
              year: entry.selectedYear,
              semester: entry.selectedSemester,
              test_name: entry.selectedTestName,
              q: entry.searchQuery,
              sort: entry.sortMode,
            });
            writeOverviewCacheEntry(activityOverviewCacheRef, 'activity', cacheKey, entry, false);
          }
        })
        .catch(() => {
          activityScopePrefetchRef.current.delete(scopeKey);
        });
    }
  }, [activityData?.availableYears, activityData?.selectedDepartment, activityData?.showYearPicker]);

  useEffect(() => {
    if (!activityData) return;
    if (activityData.showDepartmentPicker || activityData.showYearPicker) return;
    if (!activityData.selectedDepartment || !activityData.selectedYear) return;
    void prefetchActivityScopeCombos(activityData);
  }, [
    activityData?.selectedDepartment,
    activityData?.selectedYear,
    activityData?.showDepartmentPicker,
    activityData?.showYearPicker,
    activityData?.testStatus,
  ]);

  useEffect(() => {
    if (!activityData || activityData.showDepartmentPicker) return;
    void warmActivityScopeReport({
      department: activityData.selectedDepartment || undefined,
      year: activityData.selectedYear || null,
      semester: activityData.selectedSemester || undefined,
      test_name: activityData.selectedTestName || undefined,
    });
  }, [
    activityData?.selectedDepartment,
    activityData?.selectedSemester,
    activityData?.selectedTestName,
    activityData?.selectedYear,
    activityData?.showDepartmentPicker,
  ]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'cdp') return;
    if (!['admin', 'principal', 'hod'].includes(bootstrap.user.role)) return;
    void loadCdpOverview(
      cdpData?.selectedDepartment
        ? {
          department: cdpData.selectedDepartment,
          year: cdpData.selectedYear,
          semester: cdpData.selectedSemester || undefined,
          subject_id: cdpData.selectedSubjectId,
        }
        : undefined,
    );
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    const viewer = bootstrap?.user;
    if (!viewer) return;
    if (!['admin', 'principal', 'hod', 'deo'].includes(viewer.role)) return;

    const warmupKey = `${viewer.email}:${viewer.role}`;
    if (tabWarmupKeyRef.current === warmupKey) return;
    tabWarmupKeyRef.current = warmupKey;

    const timer = window.setTimeout(() => {
      const warmers: Array<Promise<unknown>> = [];
      const cacheDashboard = readOverviewCacheEntry(dashboardOverviewCacheRef, 'dashboard', buildDashboardOverviewCacheKey());
      if (['admin', 'principal', 'hod'].includes(viewer.role) && (!cacheDashboard || Date.now() - cacheDashboard.timestamp >= SCOPE_CACHE_TTL_MS)) {
        warmers.push(
          getDashboardOverview().then((payload) => {
            writeOverviewCacheEntry(dashboardOverviewCacheRef, 'dashboard', buildDashboardOverviewCacheKey(), payload);
          }),
        );
      }

      const reportsCacheKey = buildReportsOverviewCacheKey();
      const cachedReports = readOverviewCacheEntry(reportsOverviewCacheRef, 'reports', reportsCacheKey);
      if (!cachedReports || Date.now() - cachedReports.timestamp >= SCOPE_CACHE_TTL_MS) {
        warmers.push(
          getReportsOverview().then((payload) => {
            writeOverviewCacheEntry(reportsOverviewCacheRef, 'reports', reportsCacheKey, payload);
          }),
        );
      }

      const activityCacheKey = buildActivityOverviewCacheKey();
      const cachedActivity = readOverviewCacheEntry(activityOverviewCacheRef, 'activity', activityCacheKey);
      if (!cachedActivity || Date.now() - cachedActivity.timestamp >= SCOPE_CACHE_TTL_MS) {
        warmers.push(
          getActivityOverview().then((payload) => {
            writeOverviewCacheEntry(
              activityOverviewCacheRef,
              'activity',
              activityCacheKey,
              payload,
              shouldPersistActivityOverviewPayload(payload),
            );
          }),
        );
      }

      const cdpCacheKey = buildCdpOverviewCacheKey();
      const cachedCdp = readOverviewCacheEntry(cdpOverviewCacheRef, 'cdp', cdpCacheKey);
      if (['admin', 'principal', 'hod'].includes(viewer.role) && (!cachedCdp || Date.now() - cachedCdp.timestamp >= SCOPE_CACHE_TTL_MS)) {
        warmers.push(
          getCdpOverview().then((payload) => {
            writeOverviewCacheEntry(cdpOverviewCacheRef, 'cdp', cdpCacheKey, payload);
          }),
        );
      }

      const usersCacheKey = buildUsersOverviewCacheKey();
      const cachedUsers = readOverviewCacheEntry(usersOverviewCacheRef, 'users', usersCacheKey);
      if (['admin', 'principal', 'deo'].includes(viewer.role) && (!cachedUsers || Date.now() - cachedUsers.timestamp >= SCOPE_CACHE_TTL_MS)) {
        warmers.push(
          getUsers().then((payload) => {
            writeOverviewCacheEntry(usersOverviewCacheRef, 'users', usersCacheKey, payload);
          }),
        );
      }

      void Promise.allSettled(warmers);
    }, 250);

    return () => window.clearTimeout(timer);
  }, [bootstrap?.user?.email, bootstrap?.user?.role]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'messages') return;
    if (!['admin', 'hod', 'deo'].includes(bootstrap.user.role)) return;
    if (adminMessagesData) return;
    void loadAdminMessages(undefined, DEFAULT_ADMIN_MESSAGES_LIMIT);
  }, [bootstrap?.user, activeTab, adminMessagesData]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'monitoring') return;
    if (bootstrap.user.role !== 'admin') return;
    void loadMonitoringOverview();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'database') return;
    if (!['admin', 'principal'].includes(bootstrap.user.role)) return;
    void loadDatabaseOverview();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'config') return;
    if (bootstrap.user.role !== 'admin') return;
    void loadConfigOverview();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user) return;
    if (activeTab !== 'server-console') return;
    if (bootstrap.user.role !== 'admin') return;
    void loadServerConsole();
  }, [bootstrap?.user, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user || bootstrap.user.role !== 'counselor') return;
    setCounselorOverview(bootstrap.counselorOverview || null);
    setCounselorTests(Array.isArray(bootstrap.counselorTests) ? bootstrap.counselorTests : []);
  }, [bootstrap]);

  useEffect(() => {
    if (!bootstrap?.user || bootstrap.user.role !== 'counselor') return;
    void refreshCounselorOverview();
    void refreshCounselorTests();
  }, [bootstrap?.user?.email]);

  useEffect(() => {
    if (counselorSendReturnRestoreRef.current) return;
    if (!bootstrap?.user || bootstrap.user.role !== 'counselor') return;
    if (!shouldRestoreSendReturnState()) return;
    const returnState = consumeSendReturnState();
    counselorSendReturnRestoreRef.current = true;
    if (!returnState) return;
    if (returnState.kind === 'report') {
      void openCounselorSendPage(returnState.id, 'web');
      return;
    }
    void openCounselorNoticeSendPage(returnState.id, 'web');
  }, [bootstrap?.user]);

  useEffect(() => {
    if (!bootstrap?.user || bootstrap.user.role !== 'counselor') return;
    if (activeTab !== 'recent-tests' && activeTab !== 'test-database') return;
    void refreshCounselorOverview();
    void refreshCounselorTests();
  }, [bootstrap?.user?.email, activeTab]);

  useEffect(() => {
    if (!bootstrap?.user || bootstrap.user.role !== 'counselor') return;
    if (activeTab !== 'message-history') return;
    void refreshCounselorMessages();
  }, [bootstrap?.user?.email, activeTab]);

  useEffect(() => {
    if (!counselorSendPage) return;
    counselorSendVarsRef.current = { ...counselorSendVarsRef.current, ...counselorSendVars };
    try {
      localStorage.setItem(
        `send_common_vars_${counselorSendPage.testId}`,
        JSON.stringify({
          test_name: counselorSendVars.test_name,
          semester: counselorSendVars.semester,
          batch_name: counselorSendVars.batch_name,
          template: counselorSendVars.template,
        }),
      );
    } catch {
      // Ignore storage failures.
    }
  }, [counselorSendPage, counselorSendVars.batch_name, counselorSendVars.semester, counselorSendVars.template, counselorSendVars.test_name]);

  useEffect(() => {
    if (!counselorNoticeSendPage) return;
    counselorNoticeSendVarsRef.current = { ...counselorNoticeSendVarsRef.current, ...counselorNoticeSendVars };
    try {
      localStorage.setItem(
        `notice_send_vars_${counselorNoticeSendPage.noticeId}`,
        JSON.stringify({
          title: counselorNoticeSendVars.title,
          text: counselorNoticeSendVars.text,
          template: counselorNoticeSendVars.template,
        }),
      );
    } catch {
      // Ignore storage failures.
    }
  }, [counselorNoticeSendPage, counselorNoticeSendVars.template, counselorNoticeSendVars.text, counselorNoticeSendVars.title]);

  useEffect(() => {
    if (!counselorNoticeSendPage) return;
    const nextAutoTemplate = buildDefaultNoticeMessage(
      counselorNoticeSendVars.title,
      counselorNoticeSendVars.text,
      counselorNoticeSendPage.attachmentLinksText,
    );
    setCounselorNoticeAutoTemplate((prev) => (prev === nextAutoTemplate ? prev : nextAutoTemplate));
    if (!counselorNoticeTemplateEdited || counselorNoticeSendVars.template === counselorNoticeAutoTemplate) {
      counselorNoticeSendVarsRef.current = { ...counselorNoticeSendVarsRef.current, template: nextAutoTemplate };
      setCounselorNoticeSendVars((prev) => (prev.template === nextAutoTemplate ? prev : { ...prev, template: nextAutoTemplate }));
    }
  }, [
    counselorNoticeAutoTemplate,
    counselorNoticeSendPage,
    counselorNoticeSendVars.template,
    counselorNoticeSendVars.text,
    counselorNoticeSendVars.title,
    counselorNoticeTemplateEdited,
  ]);

  useEffect(() => {
    const onFocus = () => {
      if (counselorBatchRunningRef.current) {
        window.setTimeout(() => {
          if (counselorBatchRunningRef.current) {
            counselorBatchRunningRef.current = false;
            setCounselorBatchRunning(false);
            if (counselorBatchTimerRef.current) {
              window.clearTimeout(counselorBatchTimerRef.current);
              counselorBatchTimerRef.current = null;
            }
          }
        }, 500);
      }

      if (counselorNoticeBatchRunningRef.current) {
        window.setTimeout(() => {
          if (counselorNoticeBatchRunningRef.current) {
            counselorNoticeBatchRunningRef.current = false;
            setCounselorNoticeBatchRunning(false);
            if (counselorNoticeBatchTimerRef.current) {
              window.clearTimeout(counselorNoticeBatchTimerRef.current);
              counselorNoticeBatchTimerRef.current = null;
            }
          }
        }, 500);
      }
    };

    window.addEventListener('focus', onFocus);
    return () => window.removeEventListener('focus', onFocus);
  }, []);

  useEffect(() => {
    if (!counselorSendVerify) return;
    if (counselorSendVerify.completed) return;
    if (isMobileUi()) {
      void openCounselorSendPage(counselorSendVerify.testId, 'app');
      return;
    }

    const markAppFound = () => {
      setCounselorSendVerify((prev) => {
        if (!prev || prev.completed || prev.appFound) return prev;
        return {
          ...prev,
          appFound: true,
          completed: true,
          tone: 'success',
          title: 'WhatsApp app found.',
          body: 'Window focus changed while opening app. You can continue with app mode or use web mode.',
        };
      });
    };

    const markAppNotFound = () => {
      setCounselorSendVerify((prev) => {
        if (!prev || prev.completed) return prev;
        return {
          ...prev,
          completed: true,
          tone: 'error',
          title: 'WhatsApp app was not found.',
          body: 'No focus change detected in 5 seconds. We recommend installing the app, or continue with web mode.',
        };
      });
    };

    const onVisibility = () => {
      if (document.visibilityState === 'hidden') markAppFound();
    };
    const onBlur = () => markAppFound();
    const onPageHide = () => markAppFound();

    document.addEventListener('visibilitychange', onVisibility);
    window.addEventListener('blur', onBlur);
    window.addEventListener('pagehide', onPageHide);

    const triggerTimer = window.setTimeout(() => {
      openWhatsAppAppDirect('whatsapp://send');
    }, 2500);
    const failTimer = window.setTimeout(() => markAppNotFound(), 7500);

    return () => {
      window.clearTimeout(triggerTimer);
      window.clearTimeout(failTimer);
      document.removeEventListener('visibilitychange', onVisibility);
      window.removeEventListener('blur', onBlur);
      window.removeEventListener('pagehide', onPageHide);
    };
  }, [counselorSendVerify]);

  useEffect(() => {
    if (!counselorNoticeSendVerify) return;
    if (counselorNoticeSendVerify.completed) return;
    if (isMobileUi()) {
      void openCounselorNoticeSendPage(counselorNoticeSendVerify.noticeId, 'app');
      return;
    }

    const markAppFound = () => {
      setCounselorNoticeSendVerify((prev) => {
        if (!prev || prev.completed || prev.appFound) return prev;
        return {
          ...prev,
          appFound: true,
          completed: true,
          tone: 'success',
          title: 'WhatsApp app found.',
          body: 'Window focus changed while opening app. You can continue with app mode or use web mode.',
        };
      });
    };

    const markAppNotFound = () => {
      setCounselorNoticeSendVerify((prev) => {
        if (!prev || prev.completed) return prev;
        return {
          ...prev,
          completed: true,
          tone: 'error',
          title: 'WhatsApp app was not found.',
          body: 'No focus change detected in 5 seconds. We recommend installing the app, or continue with web mode.',
        };
      });
    };

    const onVisibility = () => {
      if (document.visibilityState === 'hidden') markAppFound();
    };
    const onBlur = () => markAppFound();
    const onPageHide = () => markAppFound();

    document.addEventListener('visibilitychange', onVisibility);
    window.addEventListener('blur', onBlur);
    window.addEventListener('pagehide', onPageHide);

    const triggerTimer = window.setTimeout(() => {
      openWhatsAppAppDirect('whatsapp://send');
    }, 2500);
    const failTimer = window.setTimeout(() => markAppNotFound(), 7500);

    return () => {
      window.clearTimeout(triggerTimer);
      window.clearTimeout(failTimer);
      document.removeEventListener('visibilitychange', onVisibility);
      window.removeEventListener('blur', onBlur);
      window.removeEventListener('pagehide', onPageHide);
    };
  }, [counselorNoticeSendVerify]);

  const filteredUsers = useMemo(() => {
    const query = deferredUserSearch.trim().toLowerCase();
    const filtered = users.filter((row) => {
      const matchesQuery = !query || [row.name, row.email, row.role, row.department || '', String(row.year_level || '')].join(' ').toLowerCase().includes(query);
      const matchesDepartment = !userFilterDepartment || String(row.department || '').toUpperCase() === userFilterDepartment.toUpperCase();
      const matchesRole = !userFilterRole || row.role === userFilterRole;
      const rowStatus = row.is_active && !row.is_locked ? 'active' : 'inactive';
      const matchesStatus = !userFilterStatus || rowStatus === userFilterStatus;
      const matchesYear = !userFilterYear || String(row.year_level || '') === userFilterYear;
      const matchesStudentList =
        !userFilterStudentList
        || (userFilterStudentList === 'with_students' && (row.student_count || 0) > 0)
        || (userFilterStudentList === 'no_students' && (row.student_count || 0) === 0);
      return matchesQuery && matchesDepartment && matchesRole && matchesStatus && matchesYear && matchesStudentList;
    });

    const sorted = [...filtered];
    sorted.sort((a, b) => {
      if (userSortBy === 'name_desc') return a.name.localeCompare(b.name) * -1;
      if (userSortBy === 'date_added') return String(b.created_at || '').localeCompare(String(a.created_at || ''));
      if (userSortBy === 'role') return getRoleOptionLabel(a.role, a.designation).localeCompare(getRoleOptionLabel(b.role, b.designation));
      if (userSortBy === 'department') return String(a.department || '').localeCompare(String(b.department || ''));
      if (userSortBy === 'year') return Number(a.year_level || 0) - Number(b.year_level || 0);
      return a.name.localeCompare(b.name);
    });
    return sorted;
  }, [deferredUserSearch, userFilterDepartment, userFilterRole, userFilterStatus, userFilterStudentList, userFilterYear, userSortBy, users]);
  const managedUserDomain = useMemo(
    () => resolveManagedUserDomainClient(configData?.appConfig || bootstrap?.appConfig || null),
    [bootstrap?.appConfig, configData?.appConfig],
  );
  const normalizedUserCreateEmail = useMemo(
    () => normalizeManagedUserEmailClient(userCreateForm.email),
    [userCreateForm.email],
  );
  const userCreateExistingAccounts = useMemo(
    () => normalizedUserCreateEmail ? users.filter((row) => normalizeManagedUserEmailClient(row.email) === normalizedUserCreateEmail) : [],
    [normalizedUserCreateEmail, users],
  );
  const userCreateAvailableRoles = useMemo(() => {
    const takenRoles = new Set(userCreateExistingAccounts.map((row) => row.role));
    return userAssignableRoles.filter((role) => !takenRoles.has(role));
  }, [userAssignableRoles, userCreateExistingAccounts]);
  const userCreateEmailExists = userCreateExistingAccounts.length > 0;
  const userCreateEmailDomainValid = !normalizedUserCreateEmail || normalizedUserCreateEmail.endsWith(`@${managedUserDomain}`);
  const otpPolicyChanged = useMemo(
    () => Boolean(configData) && Boolean(configForm.require_otp_on_login) !== toBooleanString(configData?.appConfig?.require_otp_on_login),
    [configData, configData?.appConfig?.require_otp_on_login, configForm.require_otp_on_login],
  );
  const configFormDirty = useMemo(
    () => Boolean(configData) && JSON.stringify(configForm) !== configBaselineSnapshot,
    [configBaselineSnapshot, configData, configForm],
  );
  const linkedUserGroupRecords = useMemo(
    () => linkedUserGroupEmail ? users.filter((row) => normalizeManagedUserEmailClient(row.email) === normalizeManagedUserEmailClient(linkedUserGroupEmail)) : [],
    [linkedUserGroupEmail, users],
  );
  useEffect(() => {
    const authUser = bootstrap?.user || null;
    if (userCreateDraftLoadedRef.current) return;
    if (!authUser || !['admin', 'deo'].includes(authUser.role)) return;
    userCreateDraftLoadedRef.current = true;
    try {
      const raw = window.localStorage.getItem(USER_CREATE_DRAFT_STORAGE_KEY);
      if (!raw) return;
      const stored = JSON.parse(raw) as Partial<typeof userCreateForm>;
      setUserCreateForm((prev) => ({
        ...prev,
        ...stored,
        scope_pairs: Array.isArray(stored?.scope_pairs) ? stored.scope_pairs.filter((value): value is string => typeof value === 'string') : prev.scope_pairs,
      }));
    } catch {
      // Ignore malformed drafts.
    }
  }, [bootstrap?.user]);
  useEffect(() => {
    const authUser = bootstrap?.user || null;
    if (!authUser || !['admin', 'deo'].includes(authUser.role)) return;
    try {
      window.localStorage.setItem(USER_CREATE_DRAFT_STORAGE_KEY, JSON.stringify(userCreateForm));
    } catch {
      // Ignore localStorage write failures.
    }
  }, [bootstrap?.user, userCreateForm]);
  useEffect(() => {
    if (!userCreateEmailExists) return;
    const existingName = String(userCreateExistingAccounts[0]?.name || '').trim();
    setUserCreateForm((prev) => {
      const nextRole = userCreateAvailableRoles.includes(prev.role) ? prev.role : (userCreateAvailableRoles[0] || prev.role);
      const nextState = {
        ...prev,
        name: existingName || prev.name,
        password: '',
        confirm_password: '',
        role: nextRole,
        designation: nextRole === 'principal' ? (String(prev.designation || '').trim() || 'Higher Official') : '',
      };
      if (
        nextState.name === prev.name
        && nextState.password === prev.password
        && nextState.confirm_password === prev.confirm_password
        && nextState.role === prev.role
        && nextState.designation === prev.designation
      ) {
        return prev;
      }
      return nextState;
    });
  }, [userCreateAvailableRoles, userCreateEmailExists, userCreateExistingAccounts]);
  useEffect(() => {
    if (linkedUserGroupEmail && !linkedUserGroupRecords.length) {
      setLinkedUserGroupEmail('');
    }
  }, [linkedUserGroupEmail, linkedUserGroupRecords.length]);
  const filteredResetUsers = useMemo(() => {
    const allUsers = configData?.resetUsers || [];
    const query = deferredResetUserSearch.trim().toLowerCase();
    const filtered = allUsers.filter((row) => {
      const matchesQuery = !query || [row.name, row.email, row.role, row.department || ''].join(' ').toLowerCase().includes(query);
      const matchesDepartment = !resetUserDepartmentFilter || String(row.department || '').toUpperCase() === resetUserDepartmentFilter.toUpperCase();
      const matchesYear = !resetUserYearFilter || String(row.year_level || '') === resetUserYearFilter;
      return matchesQuery && matchesDepartment && matchesYear;
    });
    if (!query && !resetUserDepartmentFilter && !resetUserYearFilter) return filtered.slice(0, 12);
    return filtered.slice(0, 20);
  }, [configData?.resetUsers, deferredResetUserSearch, resetUserDepartmentFilter, resetUserYearFilter]);
  const resetFilterDepartments = useMemo(
    () => Array.from(new Set((configData?.resetUsers || []).map((row) => String(row.department || '').trim()).filter(Boolean))).sort((a, b) => a.localeCompare(b)),
    [configData?.resetUsers],
  );
  const resetFilterYears = useMemo(
    () => Array.from(new Set((configData?.resetUsers || []).map((row) => Number(row.year_level || 0)).filter((value) => value > 0))).sort((a, b) => a - b),
    [configData?.resetUsers],
  );
  const filteredPreviewUsers = useMemo(() => {
    const allUsers = (configData?.resetUsers || []).filter((row) => String(row.role || '').trim().toLowerCase() !== 'admin');
    const query = previewUserSearch.trim().toLowerCase();
    if (!query) return allUsers.slice(0, 12);
    return allUsers
      .filter((row) => [row.name, row.email, row.role, row.department || ''].join(' ').toLowerCase().includes(query))
      .slice(0, 12);
  }, [configData?.resetUsers, previewUserSearch]);
  const previewUserRecord = useMemo(
    () => (configData?.resetUsers || []).find((row) => (row.account_email || row.email) === previewUserEmail) || null,
    [configData?.resetUsers, previewUserEmail],
  );
  const previewShellUser = useMemo(
    () => previewUserRecord ? {
      email: previewUserRecord.email,
      name: previewUserRecord.name,
      role: previewUserRecord.role,
      designation: previewUserRecord.designation || '',
      department: previewUserRecord.department || null,
      year_level: Number(previewUserRecord.year_level || 1) || 1,
      scopes: previewUserRecord.scopes || [],
    } : null,
    [previewUserRecord],
  );
  const previewTabs = useMemo(
    () => (previewShellUser ? getTabsForUser(previewShellUser) : []),
    [previewShellUser],
  );
  const previewDefaultTab = useMemo(
    () => (previewShellUser ? getDefaultTab(previewShellUser) : ''),
    [previewShellUser],
  );
  const previewScopeSummary = useMemo(() => {
    if (!previewShellUser) return '-';
    if (previewShellUser.role === 'counselor') {
      return `${previewShellUser.department || '-'}${previewShellUser.department ? ' • ' : ''}${formatYearLevel(previewShellUser.year_level || 1)}`;
    }
    if (previewShellUser.scopes.length) {
      return previewShellUser.scopes
        .slice(0, 8)
        .map((scope) => `${scope.department} ${formatYearLevel(scope.year_level)}`)
        .join(', ');
    }
    return previewShellUser.department || 'All Departments';
  }, [previewShellUser]);
  const noticeCompletionRows = useMemo(() => {
    const rows = [...(noticesData?.completionRows || [])];
    const query = noticeCompletionSearch.trim().toLowerCase();
    const filtered = rows.filter((row) => {
      const matchesSearch = !query || [
        row.name,
        row.email,
        row.department,
        formatYearLevel(row.year_level || 1),
        ...(row.pending_notice_titles || []),
      ].join(' ').toLowerCase().includes(query);
      const matchesDepartment = !noticeCompletionDepartment || String(row.department || '').toUpperCase() === noticeCompletionDepartment.toUpperCase();
      const matchesYear = !noticeCompletionYear || String(row.year_level || '') === noticeCompletionYear;
      return matchesSearch && matchesDepartment && matchesYear;
    });
    filtered.sort((a, b) => {
      if (noticeCompletionSort === 'name_asc') return a.name.localeCompare(b.name);
      if (noticeCompletionSort === 'name_desc') return b.name.localeCompare(a.name);
      if (noticeCompletionSort === 'department_asc') return String(a.department || '').localeCompare(String(b.department || '')) || a.year_level - b.year_level;
      if (noticeCompletionSort === 'completion_desc') return (b.completion_pct || 0) - (a.completion_pct || 0);
      if (noticeCompletionSort === 'completion_asc') return (a.completion_pct || 0) - (b.completion_pct || 0);
      if (noticeCompletionSort === 'pending_asc') return (a.pending_notice_count || 0) - (b.pending_notice_count || 0);
      return (b.pending_notice_count || 0) - (a.pending_notice_count || 0) || a.name.localeCompare(b.name);
    });
    return filtered;
  }, [noticeCompletionDepartment, noticeCompletionSearch, noticeCompletionSort, noticeCompletionYear, noticesData?.completionRows]);
  const visibleNoticeRecords = useMemo(() => {
    const query = noticeRecordSearch.trim().toLowerCase();
    const rows = [...(noticesData?.records || [])].filter((notice) => {
      if (!query) return true;
      return [
        notice.title_display,
        notice.message_preview,
        notice.created_by_name,
        notice.created_by,
        ...(notice.scope_labels || []),
      ]
        .join(' ')
        .toLowerCase()
        .includes(query);
    });

    rows.sort((a, b) => {
      if (noticeRecordSort === 'title_asc') return String(a.title_display || '').localeCompare(String(b.title_display || ''));
      if (noticeRecordSort === 'title_desc') return String(b.title_display || '').localeCompare(String(a.title_display || ''));
      if (noticeRecordSort === 'attachments_desc') return Number(b.attachment_count || 0) - Number(a.attachment_count || 0);
      if (noticeRecordSort === 'progress_desc') {
        const aProgress = bootstrap?.user?.role === 'counselor'
          ? Number(a.sent_students || 0) / Math.max(1, Number(a.student_count || a.total_students || 0))
          : Number(a.completed_counselors || 0) / Math.max(1, Number(a.total_counselors || 0));
        const bProgress = bootstrap?.user?.role === 'counselor'
          ? Number(b.sent_students || 0) / Math.max(1, Number(b.student_count || b.total_students || 0))
          : Number(b.completed_counselors || 0) / Math.max(1, Number(b.total_counselors || 0));
        return bProgress - aProgress;
      }
      return String(b.created_at || b.created_day || '').localeCompare(String(a.created_at || a.created_day || ''));
    });

    return rows;
  }, [bootstrap?.user?.role, noticeRecordSearch, noticeRecordSort, noticesData?.records]);
  const activeNoticeEdit = useMemo(() => {
    if (!noticeForm.notice_id) return null;
    if (!noticesData?.editNotice) return null;
    return noticesData.editNotice.id === noticeForm.notice_id ? noticesData.editNotice : null;
  }, [noticeForm.notice_id, noticesData?.editNotice]);
  const activityDisplayRows = useMemo(() => {
    const rows = [...(activityData?.result?.rows || [])];
    const query = String(deferredActivitySearch || '').trim().toLowerCase();
    const filtered = rows.filter((row) => {
      if (!query) return true;
      return [row.name, row.email, row.department, formatYearLevel(row.year_level || 1)]
        .join(' ')
        .toLowerCase()
        .includes(query);
    });
    filtered.sort((a, b) => {
      if (activityFilters.sort === 'name_desc') return b.name.localeCompare(a.name);
      if (activityFilters.sort === 'name_asc') return a.name.localeCompare(b.name);
      const statusCompare = (a.work_status === 'Complete' ? 1 : 0) - (b.work_status === 'Complete' ? 1 : 0);
      if (statusCompare !== 0) return statusCompare;
      if ((b.pending_count || 0) !== (a.pending_count || 0)) return (b.pending_count || 0) - (a.pending_count || 0);
      return a.name.localeCompare(b.name);
    });
    return filtered;
  }, [activityData?.result?.rows, activityFilters.sort, deferredActivitySearch]);
  const filteredMonitoringSessions = useMemo(() => {
    const rows = [...(monitoringData?.sessions || [])];
    const query = String(deferredMonitoringSearch || '').trim().toLowerCase();
    const filtered = rows.filter((session) => {
      const authMethod = String(session.auth_method || 'password').trim().toLowerCase();
      const normalizedAuth = authMethod === 'password_failed'
        ? 'password_failed'
        : authMethod === 'google_unregistered'
        ? 'google_failed'
        : authMethod.startsWith('google')
          ? 'google'
          : 'password';
      if (monitoringAuthFilter !== 'all' && normalizedAuth !== monitoringAuthFilter) return false;
      if (monitoringStatusFilter !== 'all' && String(session.status || '').trim().toLowerCase() !== monitoringStatusFilter) return false;
      if (!query) return true;
        return [
          session.name,
          session.login_email,
          session.user_email,
        session.role,
        session.department,
        session.ip_address,
        session.user_agent,
        session.status,
      ].join(' ').toLowerCase().includes(query);
    });
    const getTime = (value: string | null | undefined) => Date.parse(String(value || '').replace(' ', 'T')) || 0;
    filtered.sort((a, b) => {
      if (monitoringSortBy === 'last_activity_asc') return getTime(a.last_activity) - getTime(b.last_activity);
      if (monitoringSortBy === 'login_asc') return getTime(a.login_time) - getTime(b.login_time);
      if (monitoringSortBy === 'login_desc') return getTime(b.login_time) - getTime(a.login_time);
      return getTime(b.last_activity) - getTime(a.last_activity);
    });
    return filtered;
  }, [deferredMonitoringSearch, monitoringAuthFilter, monitoringData?.sessions, monitoringSortBy, monitoringStatusFilter]);
  const filteredMonitoringHistory = useMemo(() => {
    const rows = [...(monitoringData?.history || [])];
    const query = String(deferredMonitoringSearch || '').trim().toLowerCase();
    const filtered = rows.filter((entry) => {
      const authMethod = String(entry.auth_method || 'password').trim().toLowerCase();
      const normalizedAuth = authMethod === 'password_failed'
        ? 'password_failed'
        : authMethod === 'google_unregistered'
        ? 'google_failed'
        : authMethod.startsWith('google')
          ? 'google'
          : 'password';
      if (monitoringAuthFilter !== 'all' && normalizedAuth !== monitoringAuthFilter) return false;
      if (!query) return true;
        return [
          entry.name,
          entry.login_email,
          entry.user_email,
        entry.role,
        entry.department,
        entry.ip_address,
        entry.logout_reason,
        entry.auth_method,
      ].join(' ').toLowerCase().includes(query);
    });
    const getTime = (value: string | null | undefined) => Date.parse(String(value || '').replace(' ', 'T')) || 0;
    filtered.sort((a, b) => {
      if (monitoringSortBy === 'last_activity_asc') return getTime(a.last_activity) - getTime(b.last_activity);
      if (monitoringSortBy === 'login_asc') return getTime(a.login_time) - getTime(b.login_time);
      if (monitoringSortBy === 'login_desc') return getTime(b.login_time) - getTime(a.login_time);
      return getTime(b.last_activity) - getTime(a.last_activity);
    });
    return filtered;
  }, [deferredMonitoringSearch, monitoringAuthFilter, monitoringData?.history, monitoringSortBy]);
  const reportTestsBySemester = useMemo(() => splitTestsBySemester(reportsData?.tests || []), [reportsData]);
  const counselorVisibleTests = useMemo(() => {
    if (bootstrap?.user?.role === 'counselor' && Array.isArray(bootstrap.counselorTests)) return bootstrap.counselorTests;
    if (bootstrap?.counselorTests?.length) return bootstrap.counselorTests;
    if (counselorTests.length) return counselorTests;
    if (bootstrap?.counselorOverview?.recentTests?.length) return bootstrap.counselorOverview.recentTests;
    if (counselorOverview?.recentTests?.length) return counselorOverview.recentTests;
    return [];
  }, [bootstrap?.counselorOverview?.recentTests, bootstrap?.counselorTests, bootstrap?.user?.role, counselorOverview?.recentTests, counselorTests]);
  const counselorTestsBySemester = useMemo(() => splitTestsBySemester(counselorVisibleTests), [counselorVisibleTests]);
  const counselorDashboardRecentTests = useMemo(() => {
    if (bootstrap?.counselorOverview?.recentTests?.length) return bootstrap.counselorOverview.recentTests;
    if (counselorOverview?.recentTests?.length) return counselorOverview.recentTests;
    return counselorVisibleTests.slice(0, 2);
  }, [bootstrap?.counselorOverview?.recentTests, counselorOverview?.recentTests, counselorVisibleTests]);
  const counselorTopPerformingStudents = useMemo(() => {
    if (bootstrap?.counselorOverview?.topPerformingStudents?.length) return bootstrap.counselorOverview.topPerformingStudents;
    if (counselorOverview?.topPerformingStudents?.length) return counselorOverview.topPerformingStudents;
    return [];
  }, [bootstrap?.counselorOverview?.topPerformingStudents, counselorOverview?.topPerformingStudents]);
  const counselorStudentsNeedImprovement = useMemo(() => {
    if (bootstrap?.counselorOverview?.studentsNeedImprovement?.length) return bootstrap.counselorOverview.studentsNeedImprovement;
    if (counselorOverview?.studentsNeedImprovement?.length) return counselorOverview.studentsNeedImprovement;
    return [];
  }, [bootstrap?.counselorOverview?.studentsNeedImprovement, counselorOverview?.studentsNeedImprovement]);
  const counselorDashboardPendingNotices = useMemo(() => {
    if (bootstrap?.user?.role === 'counselor' && bootstrap.counselorOverview) return bootstrap.counselorOverview.pendingNotices || [];
    if (bootstrap?.counselorOverview?.pendingNotices?.length) return bootstrap.counselorOverview.pendingNotices;
    if (counselorOverview?.pendingNotices?.length) return counselorOverview.pendingNotices;
    return [];
  }, [bootstrap?.counselorOverview, bootstrap?.counselorOverview?.pendingNotices, bootstrap?.user?.role, counselorOverview?.pendingNotices]);

  const currentUser = bootstrap?.user || null;
  const deletedNotificationKeys = useMemo(
    () => new Set([...readDeletedNotificationKeys(currentUser), ...serverNotificationState.deletedKeys]),
    [currentUser?.email, notificationDeletedVersion, serverNotificationState.deletedKeys],
  );
  const appNotifications = useMemo(
    () => buildAppNotifications(currentUser, counselorDashboardPendingNotices, counselorVisibleTests, {
      pendingThresholdDays: Number(bootstrap?.appConfig?.notification_pending_threshold_days || 2) || 2,
      updateInfo: desktopUpdateInfo,
      appVersion: bootstrap?.appVersion,
      desktopSettings: desktopAppSettings,
      activityRows: activityData?.result?.rows || [],
      linkedCounselorNotifications: bootstrap?.linkedCounselorNotifications || null,
    }).filter((item) => !deletedNotificationKeys.has(item.key)),
    [
      activityData?.result?.rows,
      bootstrap?.appConfig?.notification_pending_threshold_days,
      bootstrap?.appVersion,
      bootstrap?.linkedCounselorNotifications,
      counselorDashboardPendingNotices,
      counselorVisibleTests,
      currentUser,
      deletedNotificationKeys,
      desktopAppSettings,
      desktopUpdateInfo,
    ],
  );
  const seenNotificationKeys = useMemo(
    () => new Set([...readSeenNotificationKeys(currentUser), ...serverNotificationState.readKeys, ...serverNotificationState.deletedKeys]),
    [currentUser?.email, notificationSeenVersion, serverNotificationState.deletedKeys, serverNotificationState.readKeys],
  );
  const unreadNotifications = useMemo(
    () => appNotifications.filter((item) => !seenNotificationKeys.has(item.key)),
    [appNotifications, seenNotificationKeys],
  );
  const unreadNotificationCount = unreadNotifications.length;
  const persistentCacheNamespace = useMemo(() => buildPersistentCacheNamespace(bootstrap), [bootstrap]);
  const canOpenFooterTemplates = currentUser?.role === 'admin' || currentUser?.role === 'deo';
  const isTestMode = Boolean(bootstrap?.testMode?.active);
  const roleSwitchOptions = roleSwitchOptionsOverride.length ? roleSwitchOptionsOverride : (bootstrap?.roleSwitchOptions || []);
  const orderedRoleSwitchOptions = useMemo(() => {
    if (!currentUser) return roleSwitchOptions;
    return [...roleSwitchOptions].sort((left, right) => {
      const leftCurrent = isCurrentRoleSwitchOption(left, currentUser);
      const rightCurrent = isCurrentRoleSwitchOption(right, currentUser);
      if (leftCurrent && !rightCurrent) return -1;
      if (!leftCurrent && rightCurrent) return 1;
      return getRoleOptionLabel(left.role, left.designation).localeCompare(getRoleOptionLabel(right.role, right.designation));
    });
  }, [currentUser, roleSwitchOptions]);
  const roleSwitchLoginDisplayEmail = normalizeSharedRoleDisplayEmail(
    String(
      currentUser?.login_email
      || orderedRoleSwitchOptions[0]?.accountEmail
      || currentUser?.email
      || '',
    ),
  );
  const hasLinkedRoleAccount = Boolean(
    (currentUser?.login_email && currentUser.login_email !== currentUser.email)
    || String(currentUser?.email || '').includes('::__shine_role__:'),
  );
  const canSwitchRoles = Boolean(currentUser && !isTestMode && !archiveViewActive && (orderedRoleSwitchOptions.length > 1 || hasLinkedRoleAccount));
  const embeddedWhatsappDesktopEnabled = isDesktopSendWorkspaceEnabled(bootstrap?.appConfig || null);
  const embeddedWhatsappDesktopFlowEnabled = embeddedWhatsappDesktopEnabled || desktopWhatsappWorkspaceStarted;
  const embeddedWhatsappWorkspaceVisible = embeddedWhatsappDesktopFlowEnabled
    && desktopWhatsappWorkspaceStarted
    && (
      (activeTab === 'test-database' && (counselorSendLoading || Boolean(counselorSendPage)))
      || (activeTab === 'notices' && (counselorNoticeSendLoading || Boolean(counselorNoticeSendPage)))
    );
  const counselorSendEmbeddedWhatsappActive = embeddedWhatsappDesktopFlowEnabled && activeTab === 'test-database' && Boolean(counselorSendPage);
  const counselorNoticeEmbeddedWhatsappActive = embeddedWhatsappDesktopFlowEnabled && activeTab === 'notices' && Boolean(counselorNoticeSendPage);
  const counselorSendDesktopWorkspaceMode = counselorSendEmbeddedWhatsappActive && (counselorSendVars.sendMode === 'app' || counselorSendVars.sendMode === 'web');
  const counselorNoticeDesktopWorkspaceMode = counselorNoticeEmbeddedWhatsappActive && (counselorNoticeSendVars.sendMode === 'app' || counselorNoticeSendVars.sendMode === 'web');
  const embeddedWhatsappSidepaneLayoutActive = false;
  const counselorSendRowCounts = useMemo(() => {
    const rows = counselorSendPage?.rows || [];
    const generated = rows.filter((row) => row.status === 'Generated').length;
    return {
      total: rows.length,
      generated,
      pending: rows.length - generated,
    };
  }, [counselorSendPage?.rows]);
  const counselorNoticeRowCounts = useMemo(() => {
    const rows = counselorNoticeSendPage?.rows || [];
    const generated = rows.filter((row) => row.status === 'Generated').length;
    return {
      total: rows.length,
      generated,
      pending: rows.length - generated,
    };
  }, [counselorNoticeSendPage?.rows]);
  const navTabs = bootstrap?.navTabs?.length ? bootstrap.navTabs : getTabsForUser(currentUser);
  const smtpIndicator = useMemo(
    () => getSmtpIndicator(bootstrap?.appConfig || null, bootstrap?.authUi || null),
    [bootstrap?.appConfig, bootstrap?.authUi],
  );
  const sidebarDepartmentCodes = useMemo(() => getUserDepartmentCodes(currentUser).slice(0, 6), [currentUser]);
  const testMetaReadOnly = Boolean(testDetail?.isMetaReadOnly ?? testDetail?.isReadOnly);
  const testMarksReadOnly = Boolean(testDetail?.isMarksReadOnly ?? testDetail?.isReadOnly);

  const loadDesktopRuntimeState = async () => {
    if (!runtimeConfig.isDesktop) return;
    const [settings, connectivity] = await Promise.all([
      getDesktopAppSettings(),
      getDesktopConnectivityState(),
    ]);
    if (settings) {
      setDesktopAppSettings(currentUser?.role === 'admin'
        ? settings
        : { ...settings, updateChecksEnabled: true, autoInstallUpdatesWhenIdle: true });
    }
    if (connectivity) setDesktopConnectivity(connectivity);
  };

  useEffect(() => {
    let cancelled = false;
    if (!currentUser) {
      setServerNotificationState({ readKeys: [], deletedKeys: [] });
      return () => {
        cancelled = true;
      };
    }
    const refreshNotificationState = async () => {
      try {
        const state = await getNotificationState();
        if (!cancelled) {
          setServerNotificationState((prev) => mergeNotificationState(prev, state));
        }
      } catch {
        if (!cancelled) setServerNotificationState({ readKeys: [], deletedKeys: [] });
      }
    };
    void refreshNotificationState();
    const timerId = window.setInterval(() => void refreshNotificationState(), 30_000);
    return () => {
      cancelled = true;
      window.clearInterval(timerId);
    };
  }, [currentUser?.email]);

  const markNotificationsRead = (keys: string[]) => {
    const uniqueKeys = normalizeNotificationKeys(keys);
    if (!uniqueKeys.length) return;
    const seen = readSeenNotificationKeys(currentUser);
    for (const key of uniqueKeys) seen.add(key);
    writeSeenNotificationKeys(currentUser, seen);
    setServerNotificationState((prev) => mergeNotificationState(prev, { readKeys: uniqueKeys }));
    setNotificationSeenVersion((prev) => prev + 1);
    void markNotificationKeysRead(uniqueKeys)
      .then((state) => setServerNotificationState((prev) => mergeNotificationState(prev, state)))
      .catch(() => undefined);
  };

  const deleteNotifications = (keys: string[]) => {
    const uniqueKeys = normalizeNotificationKeys(keys);
    if (!uniqueKeys.length) return;
    markNotificationsRead(uniqueKeys);
    const deleted = readDeletedNotificationKeys(currentUser);
    for (const key of uniqueKeys) deleted.add(key);
    writeDeletedNotificationKeys(currentUser, deleted);
    setServerNotificationState((prev) => mergeNotificationState(prev, { readKeys: uniqueKeys, deletedKeys: uniqueKeys }));
    setNotificationDeletedVersion((prev) => prev + 1);
    void deleteNotificationKeys(uniqueKeys)
      .then((state) => setServerNotificationState((prev) => mergeNotificationState(prev, state)))
      .catch(() => undefined);
  };

  const openNotificationCenter = () => {
    setNotificationCenterOpen(true);
    setLoginNotificationPrompt(null);
  };

  const saveDesktopSettingPatch = async (patch: Partial<DesktopAppSettings>) => {
    if (!runtimeConfig.isDesktop) return;
    setDesktopSettingsSaving(true);
    try {
      const nextSettings = await saveDesktopAppSettings({
        ...patch,
        role: currentUser?.role,
      } as Partial<DesktopAppSettings> & { role?: string });
      if (nextSettings) setDesktopAppSettings(nextSettings);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to save desktop settings.' });
    } finally {
      setDesktopSettingsSaving(false);
    }
  };

  const handleDesktopUpdateCheck = async () => {
    if (!runtimeConfig.isDesktop) return;
    setDesktopUpdateChecking(true);
    try {
      const result = await checkDesktopUpdate();
      if (result) setDesktopUpdateInfo(result);
      if (result?.available) {
        setFlash({ type: 'info', message: `Desktop update ${result.version} is available.` });
      } else if (result?.error) {
        setFlash({ type: 'error', message: result.error });
      } else {
        setFlash({ type: 'success', message: 'Desktop app is up to date.' });
      }
    } finally {
      setDesktopUpdateChecking(false);
    }
  };

  const handleDesktopUpdateInstall = async () => {
    if (!runtimeConfig.isDesktop) return;
    const result = await installDesktopUpdate();
    if (result?.deferred) {
      setFlash({ type: 'warning', message: result.error || 'Update install was deferred until the send workflow closes.' });
    } else if (result?.error) {
      setFlash({ type: 'error', message: result.error });
    }
  };

  useEffect(() => {
    if (!runtimeConfig.isDesktop) return;
    void loadDesktopRuntimeState();
    return onOpenDesktopSettings(() => {
      setDesktopSettingsPanelOpen(true);
      if (currentUser?.role === 'admin') {
        setActiveTab('config');
        setConfigDesktopMode('desktop');
      }
      void loadDesktopRuntimeState();
    });
  }, [currentUser?.role]);

  useEffect(() => {
    if (!currentUser) return;
    let cancelled = false;
    const loadUpdateNotification = async () => {
      try {
        const response = await fetch('/api/desktop/installer/meta', { credentials: 'include', headers: { Accept: 'application/json' } });
        if (!response.ok) return;
        const manifest = await response.json() as { version?: string; exeUrl?: string; releaseNotes?: string[] };
        const latestVersion = String(manifest.version || '').trim();
        const currentVersion = String(runtimeConfig.appVersion || bootstrap?.appVersion || '0.0.0').trim();
        if (!latestVersion || compareVersionStrings(latestVersion, currentVersion) <= 0) return;
        if (!cancelled) {
          setDesktopUpdateInfo({
            available: true,
            currentVersion,
            version: latestVersion,
            exeUrl: String(manifest.exeUrl || ''),
            releaseNotes: Array.isArray(manifest.releaseNotes) ? manifest.releaseNotes : [],
          });
        }
      } catch {
        // Update notifications are best-effort.
      }
    };
    void loadUpdateNotification();
    return () => {
      cancelled = true;
    };
  }, [bootstrap?.appVersion, currentUser?.email]);

  useEffect(() => {
    if (runtimeConfig.isDesktop || !currentUser) return;
    if (notificationCenterOpen) return;
    if (loginNotificationPrompt) return;
    const latestCritical = unreadNotifications.find((item) => item.severity === 'critical');
    if (latestCritical) {
      setLoginNotificationPrompt(latestCritical);
    }
  }, [currentUser, loginNotificationPrompt, notificationCenterOpen, unreadNotifications]);

  useEffect(() => {
    if (!runtimeConfig.isDesktop || !currentUser || !desktopAppSettings?.desktopNotificationsEnabled) return;
    const storageKey = `shine_desktop_toast_seen:${currentUser.email || currentUser.name || 'user'}`;
    let notifiedKeys = new Set<string>();
    try {
      notifiedKeys = new Set(JSON.parse(window.localStorage.getItem(storageKey) || '[]') as string[]);
    } catch {
      notifiedKeys = new Set<string>();
    }
    const notificationsToShow = unreadNotifications
      .filter((item) => !notifiedKeys.has(item.key))
      .slice(0, 5);
    if (!notificationsToShow.length) return;
    for (const item of notificationsToShow) {
      notifiedKeys.add(item.key);
      void showDesktopNotification({ title: item.title, body: item.body });
    }
    window.localStorage.setItem(storageKey, JSON.stringify(Array.from(notifiedKeys).slice(-200)));
  }, [currentUser, desktopAppSettings?.desktopNotificationsEnabled, unreadNotifications]);

  useEffect(() => {
    if (!runtimeConfig.isDesktop || !currentUser || !desktopAppSettings?.desktopNotificationsEnabled) return;
    let cancelled = false;
    const refreshDesktopNotifications = async () => {
      try {
        await refreshBootstrap();
      } catch {
        // Desktop notification refresh is best-effort.
      }
    };
    const pollSeconds = Math.max(10, Number(bootstrap?.appConfig?.desktop_notification_poll_seconds || bootstrap?.appConfig?.desktop_notification_poll_minutes || 30) || 30);
    const timerId = window.setInterval(() => {
      if (!cancelled) void refreshDesktopNotifications();
    }, pollSeconds * 1000);
    return () => {
      cancelled = true;
      window.clearInterval(timerId);
    };
  }, [
    bootstrap?.appConfig?.desktop_notification_poll_minutes,
    bootstrap?.appConfig?.desktop_notification_poll_seconds,
    currentUser?.email,
    desktopAppSettings?.desktopNotificationsEnabled,
  ]);

  useEffect(() => {
    if (!runtimeConfig.isDesktop || !currentUser || !desktopAppSettings) return;
    if (currentUser.role !== 'hod' && currentUser.role !== 'principal') return;
    if (desktopAppSettings.higherOfficialDigestDay !== getWeekdayKey()) return;
    if (activityData?.result?.rows?.length) return;
    void loadActivityOverview({
      sort: 'pending_first',
    });
  }, [activityData?.result?.rows?.length, currentUser, desktopAppSettings?.higherOfficialDigestDay, desktopAppSettings?.higherOfficialDigestScope]);

  useEffect(() => {
    if (!runtimeConfig.isDesktop) return;
    let cancelled = false;

    (async () => {
      const nextState = desktopWhatsappWorkspaceReady
        ? await getDesktopSendWorkspaceState(getDesktopSendTargetPreference(bootstrap?.appConfig || null))
        : await exitDesktopSendWorkspace(getDesktopSendTargetPreference(bootstrap?.appConfig || null));
      if (!cancelled) {
        setDesktopWhatsappState(nextState);
      }
    })();

    return () => {
      cancelled = true;
    };
  }, [bootstrap?.appConfig, desktopWhatsappWorkspaceReady]);

  useEffect(() => {
    if (!embeddedWhatsappSidepaneLayoutActive) return;
    const kind: 'report' | 'notice' = counselorSendDesktopWorkspaceMode ? 'report' : 'notice';
    const timer = window.setTimeout(() => {
      scrollDesktopWorkspaceIntoView(kind);
    }, 30);
    return () => window.clearTimeout(timer);
  }, [embeddedWhatsappSidepaneLayoutActive, counselorSendDesktopWorkspaceMode, counselorNoticeDesktopWorkspaceMode]);

  useEffect(() => {
    if (!runtimeConfig.isDesktop || !desktopWhatsappWorkspaceReady || desktopWhatsappWorkspaceStarted) return;
    let cancelled = false;

    const syncState = async () => {
      const nextState = await getDesktopSendWorkspaceState(getDesktopSendTargetPreference(bootstrap?.appConfig || null));
      if (!cancelled) {
        setDesktopWhatsappState(nextState);
      }
    };

    void syncState();
    const timerId = window.setInterval(() => {
      void syncState();
    }, 1500);

    return () => {
      cancelled = true;
      window.clearInterval(timerId);
    };
  }, [bootstrap?.appConfig, desktopWhatsappWorkspaceReady, desktopWhatsappWorkspaceStarted]);

  useEffect(() => {
    if (!runtimeConfig.isDesktop) return;
    if (!desktopWhatsappWorkspaceStarted) {
      void closeFloatingSendWindow('inactive');
      return;
    }

    let payload: FloatingSendWindowPayload | null = null;
    const themeVars = buildFloatingThemeVars(bootstrap?.appConfig || null);
    if (counselorSendDesktopWorkspaceMode && counselorSendPage) {
      payload = {
        kind: 'report',
        mode: counselorSendVarsRef.current.sendMode,
        title: counselorSendPage.meta.test_name || 'Student Send List',
        subtitle: `${counselorSendRowCounts.pending} pending | ${counselorSendRowCounts.total} students`,
        theme,
        themeVars,
        rows: counselorSendPage.rows.map((row) => ({
          regNo: row.reg_no,
          studentName: row.student_name,
          parentPhone: row.parent_phone,
          status: row.status,
          queueState: desktopReportQueueState[row.reg_no] || '',
          active: desktopWhatsappActiveTarget?.kind === 'report' && desktopWhatsappActiveTarget.regNo === row.reg_no,
          loading: desktopWhatsappLoadingRow === row.reg_no,
        })),
      };
    } else if (counselorNoticeDesktopWorkspaceMode && counselorNoticeSendPage) {
      payload = {
        kind: 'notice',
        mode: counselorNoticeSendVarsRef.current.sendMode,
        title: counselorNoticeSendPage.notice.title_display || counselorNoticeSendPage.notice.title || 'Notice Send List',
        subtitle: `${counselorNoticeRowCounts.pending} pending | ${counselorNoticeRowCounts.total} students`,
        theme,
        themeVars,
        rows: counselorNoticeSendPage.rows.map((row) => ({
          regNo: row.reg_no,
          studentName: row.student_name,
          parentPhone: row.parent_phone,
          status: row.status,
          queueState: desktopNoticeQueueState[row.reg_no] || '',
          active: desktopWhatsappActiveTarget?.kind === 'notice' && desktopWhatsappActiveTarget.regNo === row.reg_no,
          loading: desktopWhatsappLoadingRow === row.reg_no,
        })),
      };
    }

    if (payload) {
      void showFloatingSendWindow(payload).then((result) => {
        if (!result.success && result.error) {
          setFlash({ type: 'warning', message: result.error });
        }
      });
    } else {
      void closeFloatingSendWindow('inactive');
    }
  }, [
    counselorNoticeDesktopWorkspaceMode,
    counselorNoticeSendPage,
    counselorNoticeRowCounts,
    bootstrap?.appConfig,
    counselorSendDesktopWorkspaceMode,
    counselorSendPage,
    counselorSendRowCounts,
    desktopNoticeQueueState,
    desktopReportQueueState,
    desktopWhatsappActiveTarget,
    desktopWhatsappLoadingRow,
    desktopWhatsappWorkspaceStarted,
    theme,
  ]);

  useEffect(() => {
    if (!runtimeConfig.isDesktop) return;
    const offPick = onFloatingSendRequest((payload) => {
      const regNo = String(payload?.regNo || '').trim();
      if (!regNo) return;
      if (payload?.kind === 'notice') {
        const row = counselorNoticeSendPage?.rows.find((item) => item.reg_no === regNo);
        if (row) void handleCounselorNoticeDesktopQueuePick(row);
        return;
      }
      const row = counselorSendPage?.rows.find((item) => item.reg_no === regNo);
      if (row) void handleCounselorDesktopQueuePick(row);
    });
    const offClosed = onFloatingSendClosed(() => {
      setDesktopWhatsappWorkspaceStarted(false);
      setDesktopWhatsappWorkspaceReady(false);
      setDesktopWhatsappActiveTarget(null);
      setDesktopWhatsappLoadingRow(null);
      setDesktopWhatsappState((prev) => ({
        ...prev,
        active: false,
        loading: false,
        error: '',
      }));
    });
    return () => {
      offPick();
      offClosed();
    };
  }, [counselorNoticeDesktopWorkspaceMode, counselorNoticeSendPage, counselorSendPage]);

  const visibleTestDetailStudents = useMemo(() => {
    if (!testDetail?.students?.length) return [];
    const query = testDetailSearch.trim().toLowerCase();
    const filtered = !query
      ? [...testDetail.students]
      : testDetail.students.filter((student) =>
        [student.reg_no, student.student_name || '']
          .join(' ')
          .toLowerCase()
          .includes(query),
      );
    filtered.sort((a, b) => {
      if (testDetailSort === 'reg_desc') return String(b.reg_no || '').localeCompare(String(a.reg_no || ''));
      if (testDetailSort === 'name_asc') return String(a.student_name || '').localeCompare(String(b.student_name || ''));
      if (testDetailSort === 'name_desc') return String(b.student_name || '').localeCompare(String(a.student_name || ''));
      if (testDetailSort === 'gpa_desc') return readSummaryMetricNumber(b.marks, ['GPA', 'gpa', 'CGPA', 'cgpa']) - readSummaryMetricNumber(a.marks, ['GPA', 'gpa', 'CGPA', 'cgpa']);
      if (testDetailSort === 'gpa_asc') return readSummaryMetricNumber(a.marks, ['GPA', 'gpa', 'CGPA', 'cgpa']) - readSummaryMetricNumber(b.marks, ['GPA', 'gpa', 'CGPA', 'cgpa']);
      if (testDetailSort === 'failed_desc') return readSummaryMetricNumber(b.marks, ['No. of subjects failed', 'noofsubjectsfailed', 'failedsubjects']) - readSummaryMetricNumber(a.marks, ['No. of subjects failed', 'noofsubjectsfailed', 'failedsubjects']);
      if (testDetailSort === 'failed_asc') return readSummaryMetricNumber(a.marks, ['No. of subjects failed', 'noofsubjectsfailed', 'failedsubjects']) - readSummaryMetricNumber(b.marks, ['No. of subjects failed', 'noofsubjectsfailed', 'failedsubjects']);
      return String(a.reg_no || '').localeCompare(String(b.reg_no || ''));
    });
    return filtered;
  }, [testDetail, testDetailSearch, testDetailSort]);
  const userSelectableDepartments = useMemo(() => {
    if (!currentUser) return departments;
    if (currentUser.role === 'admin' || currentUser.role === 'principal') return departments.filter((department) => department.is_active);
    const allowed = new Set((userActorScopes.length ? userActorScopes : currentUser.scopes).map((scope) => scope.department.toUpperCase()));
    return departments.filter((department) => department.is_active && allowed.has(department.code.toUpperCase()));
  }, [currentUser, departments, userActorScopes]);
  const userScopeOptions = useMemo(() => {
    if (!currentUser) return [];
    if (currentUser.role === 'admin') {
      return userSelectableDepartments.flatMap((department) => [1, 2, 3, 4].map((year) => ({ department: department.code, year_level: year })));
    }
    return (userActorScopes.length ? userActorScopes : currentUser.scopes).map((scope) => ({
      department: scope.department.toUpperCase(),
      year_level: scope.year_level,
    }));
  }, [currentUser, userActorScopes, userSelectableDepartments]);

  async function applyBootstrapPayload(
    payload: BootstrapPayload,
    options?: { showBootLoader?: boolean; forceDefaultTab?: boolean; targetTab?: string },
  ) {
    const showBootLoader = Boolean(options?.showBootLoader);
    const forceDefaultTab = Boolean(options?.forceDefaultTab);
    const targetTab = String(options?.targetTab || '').trim();
    const previousEmail = String(bootstrap?.user?.email || '').toLowerCase();
    const nextEmail = String(payload.user?.email || '').toLowerCase();
    const userChanged = previousEmail !== nextEmail;
    applyThemeColors(payload.appConfig);
    seedBootstrapOverviewCaches(payload);
    const warmed = showBootLoader && payload.user ? await warmInitialUiCaches(payload, targetTab || undefined) : null;
    startTransition(() => {
      if (warmed?.dashboard) setDashboardData(warmed.dashboard);
      if (warmed?.reports) setReportsData(warmed.reports);
      if (warmed?.activity) setActivityData((prev) => prev || warmed.activity || null);
      if (warmed?.cdp) setCdpData((prev) => prev || warmed.cdp || null);
    });
    if (showBootLoader && payload.user) {
      setBootStatus('Opening workspace...');
    }
    setBootstrap(payload);
    setSessionEndNotice(payload.user ? null : (payload.sessionEndNotice || null));
    if (!payload.user || userChanged) {
      setRoleSwitchModalOpen(false);
      setRoleSwitchSelectedAccountEmail('');
      setRoleSwitchError('');
      setRoleSwitchLoading(false);
      setRoleSwitchOptionsOverride([]);
    }
    if (!payload.user) {
      clearRememberedAuthState();
      setLoginOtpState(null);
      setLoginRoleSelectionState(null);
      setActiveTab('reports');
      setUsers([]);
      setTestDetail(null);
      setTestDetailSearch('');
      setTestDetailSort('reg_asc');
      setCounselorSendPage(null);
      setCounselorSendVerify(null);
      setCounselorNoticeSendPage(null);
      setCounselorNoticeSendVerify(null);
      return;
    }
    markAuthStateAuthenticated();
    setLoginRoleSelectionState(null);
    if (userChanged) {
      setTestDetail(null);
      setTestDetailSearch('');
      setTestDetailSort('reg_asc');
      setCounselorSendPage(null);
      setCounselorSendVerify(null);
      setCounselorNoticeSendPage(null);
      setCounselorNoticeSendVerify(null);
    }
    setLoginOtpState(null);
    if (forceDefaultTab || targetTab) {
      setActiveTab(targetTab || payload.defaultTab || getDefaultTab(payload.user));
      setMobileSidebarOpen(false);
      return;
    }
    const allowHiddenConfig = activeTab === 'config' && payload.user.role === 'admin';
    if (!payload.navTabs.includes(activeTab) && !allowHiddenConfig) {
      setActiveTab(payload.defaultTab || getDefaultTab(payload.user));
    }
    setMobileSidebarOpen(false);
  }

  async function refreshBootstrap(options?: { showBootLoader?: boolean; forceDefaultTab?: boolean; targetTab?: string }) {
    const showBootLoader = Boolean(options?.showBootLoader);
    if (showBootLoader) {
      bootLoaderShownAtRef.current = typeof performance !== 'undefined' ? performance.now() : Date.now();
      setBootStatus('Loading session...');
      setBootLoading(true);
      await waitForNextPaint();
    }
    try {
      const payload = await getBootstrap();
      await applyBootstrapPayload(payload, options);
    } finally {
      if (showBootLoader) {
        await waitForMinimumBootLoaderTime();
        setBootLoading(false);
      }
    }
  }

  async function handleStartAccountTestMode(email: string) {
    try {
      await startTestMode(email);
      await refreshBootstrap({ showBootLoader: true, forceDefaultTab: true });
      setFlash({ type: 'success', message: 'Entered account test mode.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to start account test mode.' });
    }
  }

  async function handleExitTestMode() {
    try {
      await stopTestMode();
      await refreshBootstrap({ showBootLoader: true, targetTab: 'config' });
      setFlash({ type: 'success', message: 'Exited test mode.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to exit test mode.' });
    }
  }

  async function handleOpenRoleSwitchModal() {
    if (!canSwitchRoles || !currentUser) return;
    setRoleSwitchError('');
    setRoleSwitchLoading(true);
    try {
      let nextOptions = orderedRoleSwitchOptions;
      if (!nextOptions.length) {
        const payload = await getSessionRoleSwitchOptions();
        const fetchedOptions = Array.isArray(payload.options)
          ? payload.options.map((option) => ({
            accountEmail: String(option.accountEmail || ''),
            role: String(option.role || 'counselor') as Role,
            name: String(option.name || option.accountEmail || ''),
            designation: String(option.designation || ''),
            department: String(option.department || ''),
            year_level: Number(option.year_level || 1) || 1,
          }))
          : [];
        setRoleSwitchOptionsOverride(fetchedOptions);
        nextOptions = [...fetchedOptions].sort((left, right) => {
          const leftCurrent = isCurrentRoleSwitchOption(left, currentUser);
          const rightCurrent = isCurrentRoleSwitchOption(right, currentUser);
          if (leftCurrent && !rightCurrent) return -1;
          if (!leftCurrent && rightCurrent) return 1;
          return getRoleOptionLabel(left.role, left.designation).localeCompare(getRoleOptionLabel(right.role, right.designation));
        });
      }
      const nextSelection = nextOptions.find((option) => !isCurrentRoleSwitchOption(option, currentUser))?.accountEmail
        || currentUser.email
        || String(nextOptions[0]?.accountEmail || '');
      setRoleSwitchSelectedAccountEmail(nextSelection);
      setRoleSwitchModalOpen(true);
    } catch (error) {
      setRoleSwitchError(error instanceof Error ? error.message : 'Unable to load available roles.');
      setRoleSwitchModalOpen(true);
    } finally {
      setRoleSwitchLoading(false);
    }
  }

  async function handleSwitchRole(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!currentUser) return;
    if (!roleSwitchSelectedAccountEmail) {
      setRoleSwitchError('Select a role to continue.');
      return;
    }
    if (roleSwitchSelectedAccountEmail === currentUser.email) {
      setRoleSwitchModalOpen(false);
      setRoleSwitchError('');
      return;
    }
    const selectedOption = orderedRoleSwitchOptions.find((option) => option.accountEmail === roleSwitchSelectedAccountEmail) || null;
    setRoleSwitchLoading(true);
    setRoleSwitchError('');
    try {
      await switchSessionRole(roleSwitchSelectedAccountEmail);
      setRoleSwitchModalOpen(false);
      setRoleSwitchSelectedAccountEmail('');
      await refreshBootstrap({ showBootLoader: true, forceDefaultTab: true });
      setFlash({
        type: 'success',
        message: selectedOption
          ? `Switched to ${getRoleOptionLabel(selectedOption.role, selectedOption.designation)}.`
          : 'Role switched successfully.',
      });
    } catch (error) {
      setRoleSwitchError(error instanceof Error ? error.message : 'Unable to switch roles.');
    } finally {
      setRoleSwitchLoading(false);
    }
  }

  async function handleLogin(event: FormEvent<HTMLFormElement>, forceLogout = false) {
    event.preventDefault();
    setSessionEndNotice(null);
    setLoginState((prev) => ({ ...prev, loading: true, error: '', conflict: null, conflictAuthMethod: null }));
    try {
      const result = await login(loginState.identifier, loginState.password, forceLogout);
      if (result?.requiresRoleSelection) {
        setLoginRoleSelectionState({
          authMethod: (result.authMethod || 'password') as 'password' | 'google',
          loginEmail: String(result.loginEmail || loginState.identifier || ''),
          options: Array.isArray(result.options)
              ? result.options.map((option: any) => ({
                  accountEmail: String(option.accountEmail || ''),
                  role: String(option.role || 'counselor') as Role,
                  name: String(option.name || option.accountEmail || ''),
                  designation: String(option.designation || ''),
                  department: String(option.department || ''),
                  year_level: Number(option.year_level || 1) || 1,
                }))
            : [],
          selectedAccountEmail: String(result.options?.[0]?.accountEmail || ''),
        });
        setLoginState((prev) => ({ ...prev, loading: false, error: '', conflict: null, conflictAuthMethod: null }));
        return;
      }
      if (result?.requiresOtp) {
        setLoginOtpState({ maskedEmail: String(result.maskedEmail || '') });
        setLoginState((prev) => ({ ...prev, otp_code: '', loading: false, error: '', conflict: null, conflictAuthMethod: null }));
        return;
      }
      await refreshBootstrap({ showBootLoader: true, forceDefaultTab: true });
    } catch (error) {
      const err = error as Error & { payload?: any; status?: number };
      if (err.status === 409 && err.payload?.requiresForceLogout) {
        setLoginState((prev) => ({
          ...prev,
          loading: false,
          error: '',
          conflict: err.payload.existingSession || null,
          conflictAuthMethod: 'password',
        }));
        setLoginConflictInfoOpen(false);
        return;
      }
      setLoginState((prev) => ({
        ...prev,
        loading: false,
        error: err.message || 'Login failed.',
      }));
      return;
    }
    setLoginState({
      identifier: '',
      password: '',
      otp_code: '',
      loading: false,
      error: '',
      conflict: null,
      conflictAuthMethod: null,
    });
  }

  async function handleVerifyLoginOtp(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setLoginState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      const result = await verifyLoginOtp(loginState.otp_code);
      if (result?.requiresRoleSelection) {
        setLoginRoleSelectionState({
          authMethod: (result.authMethod || 'password') as 'password' | 'google',
          loginEmail: String(result.loginEmail || loginState.identifier || ''),
          options: Array.isArray(result.options)
            ? result.options.map((option) => ({
                accountEmail: String(option.accountEmail || ''),
                role: String(option.role || 'counselor') as Role,
                name: String(option.name || option.accountEmail || ''),
                designation: String(option.designation || ''),
                department: String(option.department || ''),
                year_level: Number(option.year_level || 1) || 1,
              }))
            : [],
          selectedAccountEmail: String(result.options?.[0]?.accountEmail || ''),
        });
        setLoginOtpState(null);
        setLoginState((prev) => ({
          ...prev,
          loading: false,
          error: '',
          conflict: null,
          conflictAuthMethod: null,
          otp_code: '',
        }));
        return;
      }
      await refreshBootstrap({ showBootLoader: true, forceDefaultTab: true });
      setLoginState({
        identifier: '',
        password: '',
        otp_code: '',
        loading: false,
        error: '',
        conflict: null,
        conflictAuthMethod: null,
      });
      setLoginOtpState(null);
    } catch (error) {
      const err = error as Error & { status?: number };
      if (err.status === 423 || /expired|sign in again/i.test(err.message || '')) {
        setLoginOtpState(null);
      }
      setLoginState((prev) => ({
        ...prev,
        loading: false,
        error: error instanceof Error ? error.message : 'OTP verification failed.',
      }));
    }
  }

  async function handleCompleteLoginRoleSelection(forceLogout = false) {
    if (!loginRoleSelectionState?.selectedAccountEmail) {
      setLoginState((prev) => ({ ...prev, error: 'Select a role to continue.' }));
      return;
    }
    setLoginState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      const result = await selectLoginRole(loginRoleSelectionState.selectedAccountEmail, forceLogout);
      if (result?.requiresOtp) {
        setLoginOtpState({ maskedEmail: String(result.maskedEmail || '') });
        setLoginRoleSelectionState(null);
        setLoginState((prev) => ({ ...prev, otp_code: '', loading: false, error: '', conflict: null, conflictAuthMethod: null }));
        return;
      }
      await refreshBootstrap({ showBootLoader: true, forceDefaultTab: true });
      setLoginState({
        identifier: '',
        password: '',
        otp_code: '',
        loading: false,
        error: '',
        conflict: null,
        conflictAuthMethod: null,
      });
      setLoginRoleSelectionState(null);
    } catch (error) {
      const err = error as Error & { payload?: any; status?: number };
      if (err.status === 409 && err.payload?.requiresForceLogout) {
        setLoginState((prev) => ({
          ...prev,
          loading: false,
          error: '',
          conflict: err.payload.existingSession || null,
          conflictAuthMethod: loginRoleSelectionState.authMethod,
        }));
        setLoginConflictInfoOpen(loginRoleSelectionState.authMethod === 'google' && loginConflictHasUnknownDetails(err.payload.existingSession || null));
        return;
      }
      setLoginState((prev) => ({
        ...prev,
        loading: false,
        error: err.message || 'Unable to continue with the selected role.',
      }));
    }
  }

  async function handleResendLoginOtp() {
    setLoginState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      const result = await resendLoginOtp();
      setLoginOtpState({ maskedEmail: String(result.maskedEmail || loginOtpState?.maskedEmail || '') });
      setFlash({ type: 'info', message: `A new OTP was sent to ${result.maskedEmail || 'your email'}.` });
      setLoginState((prev) => ({ ...prev, loading: false }));
    } catch (error) {
      setLoginState((prev) => ({
        ...prev,
        loading: false,
        error: error instanceof Error ? error.message : 'Unable to resend OTP.',
      }));
    }
  }

  async function handleCancelLoginOtp() {
    try {
      await cancelLoginOtp();
    } catch {
      // Ignore cancellation failures.
    }
    setLoginOtpState(null);
    setLoginRoleSelectionState(null);
    setLoginConflictInfoOpen(false);
    setLoginState((prev) => ({ ...prev, otp_code: '', loading: false, error: '', conflict: null, conflictAuthMethod: null }));
  }

  function handleGoogleLoginStart(event: ReactMouseEvent<HTMLButtonElement>) {
    event.preventDefault();
    setSessionEndNotice(null);
    setLoginRoleSelectionState(null);
    setLoginConflictInfoOpen(false);
    setLoginState((prev) => ({ ...prev, loading: false, error: '', conflict: null, conflictAuthMethod: null }));
    setForgotPasswordState((prev) => ({ ...prev, loading: false, error: '' }));
    setFlash(null);
    if (!startGoogleOauth()) {
      setFlash({ type: 'info', message: 'Google sign-in will be added to the desktop shell after the core login workflow is stabilized. Please use password login for desktop testing right now.' });
    }
  }

  async function handleResolveGoogleLoginConflict() {
    setLoginState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      await resolveGoogleLoginConflict();
      setLoginState({
        identifier: '',
        password: '',
        otp_code: '',
        loading: false,
        error: '',
        conflict: null,
        conflictAuthMethod: null,
      });
      setLoginConflictInfoOpen(false);
      await refreshBootstrap({ showBootLoader: true, forceDefaultTab: true });
      setFlash({ type: 'success', message: 'Google sign-in completed successfully.' });
    } catch (error) {
      setLoginState((prev) => ({
        ...prev,
        loading: false,
        error: error instanceof Error ? error.message : 'Unable to continue Google sign-in.',
      }));
    }
  }

  async function handleForgotPasswordRequest(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setForgotPasswordState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      const result = await requestPasswordReset(forgotPasswordState.identifier);
      setForgotPasswordState((prev) => ({
        ...prev,
        stage: 'verify',
        maskedEmail: String(result.maskedEmail || ''),
        otp_code: '',
        loading: false,
        error: '',
      }));
      setFlash({ type: 'info', message: `Password reset OTP sent to ${result.maskedEmail || 'your email'}.` });
    } catch (error) {
      setForgotPasswordState((prev) => ({
        ...prev,
        loading: false,
        error: error instanceof Error ? error.message : 'Unable to start password reset.',
      }));
    }
  }

  async function handleForgotPasswordVerify(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setForgotPasswordState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      await verifyPasswordResetOtp(forgotPasswordState.otp_code);
      setForgotPasswordState((prev) => ({ ...prev, stage: 'reset', loading: false, error: '' }));
    } catch (error) {
      setForgotPasswordState((prev) => ({
        ...prev,
        loading: false,
        error: error instanceof Error ? error.message : 'OTP verification failed.',
      }));
    }
  }

  async function handleForgotPasswordComplete(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setForgotPasswordState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      await completePasswordReset({
        new_password: forgotPasswordState.new_password,
        confirm_password: forgotPasswordState.confirm_password,
      });
      setForgotPasswordState({
        open: false,
        stage: 'request',
        identifier: '',
        maskedEmail: '',
        otp_code: '',
        new_password: '',
        confirm_password: '',
        loading: false,
        error: '',
      });
      setFlash({ type: 'success', message: 'Password reset successful. Please sign in with your new password.' });
    } catch (error) {
      setForgotPasswordState((prev) => ({
        ...prev,
        loading: false,
        error: error instanceof Error ? error.message : 'Unable to reset password.',
      }));
    }
  }

  function closeForgotPasswordModal() {
    setForgotPasswordState({
      open: false,
      stage: 'request',
      identifier: '',
      maskedEmail: '',
      otp_code: '',
      new_password: '',
      confirm_password: '',
      loading: false,
      error: '',
    });
  }

  async function handleSendSelfPasswordOtp() {
    setSelfPasswordSendingOtp(true);
    try {
      const result = await sendSelfPasswordOtp();
      setSelfPasswordOtpSentTo(String(result.maskedEmail || ''));
      setFlash({ type: 'info', message: `Password reset OTP sent to ${result.maskedEmail || 'your email'}.` });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Unable to send OTP.' });
    } finally {
      setSelfPasswordSendingOtp(false);
    }
  }

  async function handleUpdateSelfPassword(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setSelfPasswordSaving(true);
    try {
      await updateSelfPassword(selfPasswordDraft);
      setSelfPasswordDraft({
        current_password: '',
        otp_code: '',
        new_password: '',
        confirm_password: '',
      });
      setSelfPasswordOtpSentTo('');
      setSelfPasswordModalOpen(false);
      setFlash({ type: 'success', message: 'Password updated successfully.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Unable to update password.' });
    } finally {
      setSelfPasswordSaving(false);
    }
  }

  async function handleLogout() {
    if (isTestMode) {
      await handleExitTestMode();
      return;
    }
    if (archiveViewActive) {
      await handleExitArchiveView();
      return;
    }
    clearRememberedAuthState();
    try {
      window.localStorage.removeItem(USER_CREATE_DRAFT_STORAGE_KEY);
    } catch {
      // Ignore localStorage cleanup failures.
    }
    await logout();
    setLoginOtpState(null);
    await refreshBootstrap();
  }

  async function refreshDepartments() {
    setDepartmentsLoading(true);
    try {
      const payload = await getDepartments();
      setDepartments(payload.departments);
    } finally {
      setDepartmentsLoading(false);
    }
  }

  function applyUsersOverviewPayload(payload: UsersOverviewPayload) {
    startTransition(() => {
      setUsers(payload.users);
      setDepartments(payload.departments);
      setUserActorScopes(payload.actorScopes || []);
      setUserAssignableRoles(payload.assignableRoles || []);
      setUserCreateForm((prev) => ({
        ...prev,
        role: (payload.assignableRoles || []).includes(prev.role)
          ? prev.role
          : (payload.assignableRoles?.[0] || prev.role || 'counselor') as Role,
        designation: ((payload.assignableRoles || []).includes(prev.role)
          ? prev.role
          : (payload.assignableRoles?.[0] || prev.role || 'counselor')) === 'principal'
          ? (String(prev.designation || '').trim() || 'Higher Official')
          : '',
      }));
    });
  }

  async function refreshUsersOverview(options?: { preferCache?: boolean }) {
    if (!currentUser || !['admin', 'principal', 'deo'].includes(currentUser.role)) return;
    const preferCache = options?.preferCache !== false;
    const cacheKey = buildUsersOverviewCacheKey();
    const cached = preferCache ? readOverviewCacheEntry(usersOverviewCacheRef, 'users', cacheKey) : null;
    if (cached) {
      applyUsersOverviewPayload(cached.payload);
      if (Date.now() - cached.timestamp < SCOPE_CACHE_TTL_MS) return;
    }
    setUsersLoading(!cached);
    try {
      const payload = await getUsers();
      writeOverviewCacheEntry(usersOverviewCacheRef, 'users', cacheKey, payload);
      applyUsersOverviewPayload(payload);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load users.' });
    } finally {
      setUsersLoading(false);
    }
  }

  function requestConfirm(options: ConfirmDialogState) {
    return new Promise<boolean>((resolve) => {
      confirmResolverRef.current = resolve;
      setConfirmDialog(options);
    });
  }

  function closeConfirmDialog(result: boolean) {
    const resolver = confirmResolverRef.current;
    confirmResolverRef.current = null;
    setConfirmDialog(null);
    resolver?.(result);
  }

  async function loadCounselorStudents(user: UserRecord) {
    setStudentListLoading(true);
    try {
      const payload = await getCounselorStudentList(user.account_email || user.email);
      setStudentListRows(payload.students || []);
      setStudentListCounselor(user);
      setStudentListModalOpen(true);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load student list.' });
    } finally {
      setStudentListLoading(false);
    }
  }

  async function handleUploadStudentsForCounselor(file: File | null) {
    if (!studentListCounselor || !file) return;
    setStudentListSaving(true);
    try {
      const formData = new FormData();
      formData.set('student_file', file);
      const result = await uploadCounselorStudentList(studentListCounselor.email, formData);
      setFlash({ type: 'success', message: `${result.count} students uploaded successfully.` });
      setStudentUploadKey((value) => value + 1);
      await loadCounselorStudents(studentListCounselor);
      await refreshUsersOverview({ preferCache: false });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to upload student list.' });
    } finally {
      setStudentListSaving(false);
    }
  }

  async function handleSaveStudentRow(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!studentListCounselor) return;
    setStudentListSaving(true);
    try {
      await saveCounselorStudentRow(studentListCounselor.email, {
        ...studentQuickAdd,
        department: studentListCounselor.department || '',
      });
      setStudentQuickAdd({ reg_no: '', student_name: '', parent_phone: '', parent_email: '' });
      setFlash({ type: 'success', message: 'Student added successfully.' });
      await loadCounselorStudents(studentListCounselor);
      await refreshUsersOverview({ preferCache: false });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to save student.' });
    } finally {
      setStudentListSaving(false);
    }
  }

  async function handleDeleteStudentRow(regNo: string) {
    if (!studentListCounselor) return;
    const confirmed = await requestConfirm({
      title: 'Delete Student',
      message: `Delete student ${regNo}? This cannot be undone.`,
      confirmLabel: 'Delete',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fas fa-trash',
    });
    if (!confirmed) return;
    setStudentListSaving(true);
    try {
      await deleteCounselorStudentRow(studentListCounselor.email, regNo);
      setFlash({ type: 'success', message: 'Student deleted successfully.' });
      await loadCounselorStudents(studentListCounselor);
      await refreshUsersOverview({ preferCache: false });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete student.' });
    } finally {
      setStudentListSaving(false);
    }
  }

  async function handleDeleteAllStudents() {
    if (!studentListCounselor) return;
    const confirmed = await requestConfirm({
      title: 'Delete Student List',
      message: `Delete the entire student list for ${studentListCounselor.name}? This cannot be undone.`,
      confirmLabel: 'Delete All',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fas fa-trash',
    });
    if (!confirmed) return;
    setStudentListSaving(true);
    try {
      await deleteAllCounselorStudentRows(studentListCounselor.email);
      setFlash({ type: 'success', message: 'Student list deleted successfully.' });
      await loadCounselorStudents(studentListCounselor);
      await refreshUsersOverview({ preferCache: false });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete student list.' });
    } finally {
      setStudentListSaving(false);
    }
  }

  async function refreshCounselorOverview() {
    setCounselorOverviewLoading(true);
    try {
      const payload = await getCounselorOverview();
      setCounselorOverview(payload);
    } catch (error) {
      setCounselorOverview(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load counselor dashboard.' });
    } finally {
      setCounselorOverviewLoading(false);
    }
  }

  async function refreshCounselorTests() {
    setCounselorTestsLoading(true);
    try {
      const payload = await getCounselorTests();
      setCounselorTests(payload.tests);
    } catch (error) {
      setCounselorTests([]);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load counselor tests.' });
    } finally {
      setCounselorTestsLoading(false);
    }
  }

  async function refreshCounselorMessages() {
    setCounselorMessagesLoading(true);
    try {
      const payload = await getCounselorMessages();
      setCounselorMessages(payload.messages);
      setCounselorMessageStats(payload.stats);
    } catch (error) {
      setCounselorMessages([]);
      setCounselorMessageStats(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load counselor messages.' });
    } finally {
      setCounselorMessagesLoading(false);
    }
  }

  function applyNoticeEditState(editNotice: NoticeRecord | null) {
    if (!editNotice) {
      setNoticesData((prev) => (prev ? { ...prev, editNotice: null } : prev));
      setNoticeForm({
        notice_id: 0,
        notice_title: '',
        notice_message_text: '',
        notice_send_to_all: false,
        scope_pairs: [],
        remove_attachment_ids: [],
        files: [],
      });
      setNoticeFileInputKey((value) => value + 1);
      return;
    }

    setNoticeForm({
      notice_id: editNotice.id,
      notice_title: editNotice.title || '',
      notice_message_text: editNotice.message_text || '',
      notice_send_to_all: Boolean(editNotice.send_to_all),
      scope_pairs: (editNotice.scope_pairs || []).map((scope) => `${scope.department}::${scope.year_level}`),
      remove_attachment_ids: [],
      files: [],
    });
    setNoticeFileInputKey((value) => value + 1);
  }

  async function loadNotices(filters?: {
    department?: string;
    year?: number | null;
    status?: string;
    date_from?: string;
    date_to?: string;
    edit_id?: number | null;
  }) {
    setNoticesLoading(true);
    try {
      const payload = await getNoticesOverview(filters);
      setNoticesData(payload);
      setNoticeFilters({
        department: payload.filters.department || '',
        year: payload.filters.year ? String(payload.filters.year) : '',
        status: payload.filters.status || '',
        date_from: payload.filters.date_from || '',
        date_to: payload.filters.date_to || '',
      });
      applyNoticeEditState(payload.editNotice);
    } finally {
      setNoticesLoading(false);
    }
  }

  async function loadReports(department?: string, year?: number | null, options?: { preferCache?: boolean }) {
    const cacheKey = buildReportsOverviewCacheKey(department, year);
    const cached = options?.preferCache === false ? null : readOverviewCacheEntry(reportsOverviewCacheRef, 'reports', cacheKey);
    if (cached) {
      setReportsData(cached.payload);
      setTestDetail(null);
      if (Date.now() - cached.timestamp < SCOPE_CACHE_TTL_MS) return;
    }
    setReportsLoading(!cached);
    try {
      const payload = await getReportsOverview(department, year);
      writeOverviewCacheEntry(reportsOverviewCacheRef, 'reports', cacheKey, payload);
      setReportsData(payload);
      setTestDetail(null);
    } finally {
      setReportsLoading(false);
    }
  }

  useEffect(() => {
    const link = String(subjectForm.google_sheet_link || '').trim();
    const selectedDepartment = String(subjectsData?.selectedDepartment || '').trim().toUpperCase();
    const parseKey = link ? `${selectedDepartment}::${link}` : '';
    if (!link) {
      subjectParseRequestRef.current += 1;
      setSubjectLastParsedLink('');
      setSubjectParsedClasses([]);
      setSubjectParsedFaculties([]);
      setSubjectParseError('');
      setSubjectParsing(false);
      return undefined;
    }

    if (!looksLikeGoogleSheetLink(link)) {
      subjectParseRequestRef.current += 1;
      setSubjectParsedClasses([]);
      setSubjectParsedFaculties([]);
      setSubjectParseError('');
      setSubjectParsing(false);
      return undefined;
    }

    if (parseKey === subjectLastParsedLink) {
      return undefined;
    }

    setSubjectParsedClasses([]);
    setSubjectParseError('');

    const requestId = subjectParseRequestRef.current + 1;
    subjectParseRequestRef.current = requestId;

    const timeoutId = window.setTimeout(() => {
      void (async () => {
        setSubjectParsing(true);
        try {
          const parsed = await parseSubjectSheet(link, String(subjectsData?.selectedDepartment || ''));
          if (subjectParseRequestRef.current !== requestId) return;

          const parsedSections = normalizeClassSections(parsed.class_sections || []);
          const parsedFaculties = splitFacultyNames((parsed.faculty_names || []).join(' / ') || parsed.faculty_name || '');
          const parsedSuggestedAllocations = normalizeFacultyAllocations(parsed.faculty_allocations || [], parsedFaculties, parsedSections);
          if (selectedDepartment && parsedSections.length && !doClassSectionsMatchDepartment(parsedSections, selectedDepartment)) {
            setSubjectParsedClasses([]);
            setSubjectParsedFaculties(parsedFaculties);
            setSubjectParseError(`Parsed classes (${parsedSections.join(', ')}) do not match the selected department ${selectedDepartment}.`);
            setSubjectLastParsedLink(parseKey);
            setSubjectForm((prev) => ({
              ...prev,
              subject_code: parsed.subject_code || prev.subject_code,
              subject_name: parsed.subject_name || prev.subject_name,
              faculty_name: parsed.faculty_name || prev.faculty_name,
              class_sections: [],
              faculty_allocations: [],
            }));
            return;
          }
          setSubjectForm((prev) => {
            if (String(prev.google_sheet_link || '').trim() !== link) return prev;
            const nextAllocations = normalizeFacultyAllocations(
              prev.faculty_allocations.some((entry) => entry.class_sections.length) ? prev.faculty_allocations : parsedSuggestedAllocations,
              parsedFaculties,
              parsedSections,
            );
            return {
              ...prev,
              subject_code: parsed.subject_code || prev.subject_code,
              subject_name: parsed.subject_name || prev.subject_name,
              faculty_name: parsed.faculty_name || prev.faculty_name,
              class_sections: normalizeClassSections(nextAllocations.flatMap((entry) => entry.class_sections)),
              faculty_allocations: nextAllocations,
            };
          });
          setSubjectParsedClasses(parsedSections);
          setSubjectParsedFaculties(parsedFaculties);
          setSubjectParseError(parsedSections.length ? '' : 'No class sections were detected in the Daily Attendance sheet yet.');
          setSubjectLastParsedLink(parseKey);
        } catch (error) {
          if (subjectParseRequestRef.current !== requestId) return;
          setSubjectParsedClasses([]);
          setSubjectParsedFaculties([]);
          setSubjectParseError(error instanceof Error ? error.message : 'Unable to parse Google Sheet details.');
        } finally {
          if (subjectParseRequestRef.current === requestId) {
            setSubjectParsing(false);
          }
        }
      })();
    }, 650);

    return () => {
      window.clearTimeout(timeoutId);
    };
  }, [subjectForm.google_sheet_link, subjectLastParsedLink, subjectsData?.selectedDepartment]);

  useEffect(() => {
    if (!subjectParsedClasses.length) return;
    const visibleFaculties = splitFacultyNames(subjectForm.faculty_name || '').length
      ? splitFacultyNames(subjectForm.faculty_name || '')
      : subjectParsedFaculties;
    const nextAllocations = normalizeFacultyAllocations(subjectForm.faculty_allocations, visibleFaculties, subjectParsedClasses);
    const nextClassSections = normalizeClassSections(nextAllocations.flatMap((entry) => entry.class_sections));
    const currentAllocations = JSON.stringify(subjectForm.faculty_allocations);
    const normalizedAllocations = JSON.stringify(nextAllocations);
    const currentClassSections = JSON.stringify(normalizeClassSections(subjectForm.class_sections));
    const normalizedClassSections = JSON.stringify(nextClassSections);
    if (currentAllocations === normalizedAllocations && currentClassSections === normalizedClassSections) {
      return;
    }
    setSubjectForm((prev) => ({
      ...prev,
      class_sections: nextClassSections,
      faculty_allocations: nextAllocations,
    }));
  }, [subjectForm.faculty_name, subjectParsedClasses, subjectParsedFaculties]);

  function resetSubjectDraft() {
    const defaultYear = getDefaultSubjectAttendanceYear();
    setSubjectEditId(null);
    setSubjectLastParsedLink('');
    setSubjectParsedClasses([]);
    setSubjectParsedFaculties([]);
    setSubjectParseError('');
    setSubjectForm({
      subject_code: '',
      subject_name: '',
      faculty_name: '',
      google_sheet_link: '',
      academic_start_year: String(defaultYear),
      academic_end_year: String(defaultYear),
      class_sections: [],
      faculty_allocations: [],
    });
  }

  async function loadSubjects(department?: string, year?: number | null, semester?: string) {
    const cacheKey = JSON.stringify({
      department: String(department || '').trim().toUpperCase(),
      year: Number(year || 0) || 0,
      semester: String(semester || '').trim(),
    });
    const cached = subjectsOverviewCacheRef.current.get(cacheKey);
    if (cached && Date.now() - cached.timestamp < SCOPE_CACHE_TTL_MS) {
      setSubjectsData(cached.payload);
      if (!cached.payload.selectedDepartment || !cached.payload.selectedYear || !cached.payload.selectedSemester || (subjectEditId && !cached.payload.records.some((record) => record.id === subjectEditId))) {
        resetSubjectDraft();
      }
      return;
    }
    setSubjectsLoading(true);
    try {
      const payload = await getSubjectsOverview(department, year, semester);
      subjectsOverviewCacheRef.current.set(cacheKey, { timestamp: Date.now(), payload });
      setSubjectsData(payload);
      if (!payload.selectedDepartment || !payload.selectedYear || !payload.selectedSemester || (subjectEditId && !payload.records.some((record) => record.id === subjectEditId))) {
        resetSubjectDraft();
      }
    } catch (error) {
      setSubjectsData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load subjects.' });
    } finally {
      setSubjectsLoading(false);
    }
  }

  async function loadCdpOverview(filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    subject_id?: number | null;
  }, options?: { preferCache?: boolean }) {
    const cacheKey = buildCdpOverviewCacheKey(filters);
    const cached = options?.preferCache === false ? null : readOverviewCacheEntry(cdpOverviewCacheRef, 'cdp', cacheKey);
    if (cached) {
      setCdpData(cached.payload);
      if (Date.now() - cached.timestamp < SCOPE_CACHE_TTL_MS) return;
    }
    setCdpLoading(!cached);
    try {
      const payload = await getCdpOverview(filters);
      writeOverviewCacheEntry(cdpOverviewCacheRef, 'cdp', cacheKey, payload);
      setCdpData(payload);
    } catch (error) {
      setCdpData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load CDP overview.' });
    } finally {
      setCdpLoading(false);
    }
  }

  async function rebuildCdpScopeOverview(filters: {
    department: string;
    year: number;
    semester: string;
    subject_id?: number | null;
  }) {
    setCdpLoading(true);
    setCdpData(null);
    try {
      const payload = await rebuildCdpScope(filters);
      invalidateOverviewCaches(['cdp']);
      const cacheKey = buildCdpOverviewCacheKey({
        department: payload.selectedDepartment,
        year: payload.selectedYear,
        semester: payload.selectedSemester,
        subject_id: payload.selectedSubjectId,
      });
      writeOverviewCacheEntry(cdpOverviewCacheRef, 'cdp', cacheKey, payload);
      setCdpData(payload);
    } catch (error) {
      setCdpData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to rebuild CDP scope.' });
    } finally {
      setCdpLoading(false);
    }
  }

  function beginSubjectEdit(subject: SubjectRecord) {
    setSubjectEditId(subject.id);
    setSubjectLastParsedLink('');
    setSubjectParsedClasses([]);
    setSubjectParsedFaculties(splitFacultyNames(subject.faculty_name || ''));
    setSubjectParseError('');
    setSubjectForm({
      subject_code: subject.subject_code || '',
      subject_name: subject.subject_name || '',
      faculty_name: subject.faculty_name || '',
      google_sheet_link: subject.google_sheet_link || '',
      academic_start_year: String(subject.academic_start_year || ''),
      academic_end_year: String(subject.academic_end_year || ''),
      class_sections: subject.class_sections || [],
      faculty_allocations: subject.faculty_allocations || [],
    });
  }

  async function handleSaveSubject(event: FormEvent) {
    event.preventDefault();
    if (!subjectsData?.selectedDepartment || !subjectsData.selectedYear) return;
    const academicStartYear = Number(subjectForm.academic_start_year);
    const academicEndYear = Number(subjectForm.academic_end_year);
    let effectiveParsedClasses = subjectParsedClasses;
    let effectiveParsedFaculties = subjectParsedFaculties;
    if (!effectiveParsedClasses.length && looksLikeGoogleSheetLink(String(subjectForm.google_sheet_link || '').trim())) {
      try {
        const parsed = await parseSubjectSheet(String(subjectForm.google_sheet_link || '').trim(), String(subjectsData.selectedDepartment || ''));
        effectiveParsedClasses = normalizeClassSections(parsed.class_sections || []);
        effectiveParsedFaculties = splitFacultyNames((parsed.faculty_names || []).join(' / ') || parsed.faculty_name || '');
        const parsedSuggestedAllocations = normalizeFacultyAllocations(parsed.faculty_allocations || [], effectiveParsedFaculties, effectiveParsedClasses);
        setSubjectParsedClasses(effectiveParsedClasses);
        setSubjectParsedFaculties(effectiveParsedFaculties);
        setSubjectParseError(effectiveParsedClasses.length ? '' : 'No class sections were detected in the Daily Attendance sheet yet.');
        if (!subjectForm.faculty_allocations.some((entry) => entry.class_sections.length) && parsedSuggestedAllocations.length) {
          setSubjectForm((prev) => ({
            ...prev,
            class_sections: normalizeClassSections(parsedSuggestedAllocations.flatMap((entry) => entry.class_sections)),
            faculty_allocations: parsedSuggestedAllocations,
          }));
        }
      } catch (error) {
        setSubjectParseError(error instanceof Error ? error.message : 'Unable to parse Google Sheet details.');
      }
    }
    const resolvedFacultyNames = splitFacultyNames(subjectForm.faculty_name || '').length
      ? splitFacultyNames(subjectForm.faculty_name || '')
      : effectiveParsedFaculties;
    const resolvedAllocations = normalizeFacultyAllocations(subjectForm.faculty_allocations, resolvedFacultyNames, effectiveParsedClasses);
    const resolvedClassSections = normalizeClassSections(resolvedAllocations.flatMap((entry) => entry.class_sections));

    if (!academicStartYear || !academicEndYear || academicStartYear < 2000 || academicEndYear < academicStartYear || academicEndYear > academicStartYear + 1) {
      setFlash({ type: 'error', message: 'Enter a valid attendance year range like 2025 and 2026, or use the same year for both fields when the sheet stays in one calendar year.' });
      return;
    }
    if (!resolvedAllocations.length || !resolvedClassSections.length) {
      setFlash({ type: 'error', message: 'Allocate at least one parsed class to the faculty members for this subject.' });
      return;
    }
    const missingFacultyAllocation = resolvedAllocations.find((entry) => !entry.class_sections.length);
    if (missingFacultyAllocation) {
      setFlash({ type: 'error', message: `Allocate at least one class to ${missingFacultyAllocation.faculty_name}.` });
      return;
    }

    setSubjectSaving(true);
    try {
      setSubjectForm((prev) => ({
        ...prev,
        class_sections: resolvedClassSections,
        faculty_allocations: resolvedAllocations,
      }));
      if (subjectEditId) {
        await updateSubject(subjectEditId, {
          subject_code: subjectForm.subject_code,
          subject_name: subjectForm.subject_name,
          faculty_name: subjectForm.faculty_name,
          google_sheet_link: subjectForm.google_sheet_link,
          semester: subjectsData.selectedSemester,
          academic_start_year: academicStartYear,
          academic_end_year: academicEndYear,
          class_sections: resolvedClassSections,
          faculty_allocations: resolvedAllocations,
        });
        setFlash({ type: 'success', message: 'Subject updated successfully.' });
      } else {
        await createSubject({
          subject_code: subjectForm.subject_code,
          subject_name: subjectForm.subject_name,
          faculty_name: subjectForm.faculty_name,
          google_sheet_link: subjectForm.google_sheet_link,
          department: subjectsData.selectedDepartment,
          year_level: subjectsData.selectedYear,
          semester: subjectsData.selectedSemester,
          academic_start_year: academicStartYear,
          academic_end_year: academicEndYear,
          class_sections: resolvedClassSections,
          faculty_allocations: resolvedAllocations,
        });
        setFlash({ type: 'success', message: 'Subject created successfully.' });
      }
      subjectsOverviewCacheRef.current.clear();
      invalidateOverviewCaches(['cdp']);
      resetSubjectDraft();
      await loadSubjects(subjectsData.selectedDepartment, subjectsData.selectedYear, subjectsData.selectedSemester);
      if (activeTab === 'cdp') {
        await rebuildCdpScopeOverview({
          department: subjectsData.selectedDepartment,
          year: subjectsData.selectedYear,
          semester: subjectsData.selectedSemester,
        });
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to save subject.' });
    } finally {
      setSubjectSaving(false);
    }
  }

  async function handleDeleteSubject(subject: SubjectRecord) {
    const confirmed = await requestConfirm({
      title: 'Delete Subject',
      message: `Delete ${subject.subject_code} from ${subject.department} ${formatYearLevel(subject.year_level)}?`,
      confirmLabel: 'Delete Subject',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fa-trash',
    });
    if (!confirmed) return;

    try {
      await deleteSubject(subject.id);
      subjectsOverviewCacheRef.current.clear();
      invalidateOverviewCaches(['cdp']);
      if (subjectEditId === subject.id) {
        resetSubjectDraft();
      }
      setFlash({ type: 'success', message: 'Subject deleted successfully.' });
      await loadSubjects(subject.department, subject.year_level, subject.semester);
      if (cdpData?.selectedDepartment === subject.department && cdpData?.selectedYear === subject.year_level && cdpData?.selectedSemester === subject.semester) {
        await rebuildCdpScopeOverview({ department: subject.department, year: subject.year_level, semester: subject.semester });
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete subject.' });
    }
  }

  async function loadDashboardOverview(options?: { preferCache?: boolean }) {
    const cacheKey = buildDashboardOverviewCacheKey();
    const cached = options?.preferCache === false ? null : readOverviewCacheEntry(dashboardOverviewCacheRef, 'dashboard', cacheKey);
    if (cached) {
      setDashboardData(cached.payload);
      if (Date.now() - cached.timestamp < SCOPE_CACHE_TTL_MS) return;
    }
    setDashboardLoading(!cached);
    try {
      const payload = await getDashboardOverview();
      writeOverviewCacheEntry(dashboardOverviewCacheRef, 'dashboard', cacheKey, payload);
      setDashboardData(payload);
    } catch (error) {
      setDashboardData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load dashboard overview.' });
    } finally {
      setDashboardLoading(false);
    }
  }

  function applyActivityOverviewPayload(payload: ActivityOverviewPayload) {
    const scopeSeedKey = buildActivityScopeSeedKey(payload);
    if (payload.prefetchedResults?.length && scopeSeedKey && !activityScopeSeededRef.current.has(scopeSeedKey)) {
      activityScopeSeededRef.current.add(scopeSeedKey);
      const basePayload = stripActivityPrefetchedResults(payload);
      for (const entry of payload.prefetchedResults || []) {
        const cacheKey = buildActivityOverviewCacheKey({
          department: entry.department,
          year: entry.year_level,
          semester: entry.semester,
          test_name: entry.test_name,
          q: '',
          sort: 'pending_first',
        });
        writeOverviewCacheEntry(activityOverviewCacheRef, 'activity', cacheKey, {
          ...basePayload,
          selectedDepartment: entry.department,
          selectedYear: entry.year_level,
          selectedSemester: entry.semester,
          selectedTestName: entry.test_name,
          searchQuery: '',
          sortMode: 'pending_first',
          showDepartmentPicker: false,
          showYearPicker: false,
          showSemesterPicker: false,
          result: entry,
        }, false);
      }
    }
    const nextPayload = stripActivityPrefetchedResults(payload);
    startTransition(() => {
      setActivityData(nextPayload);
      setActivityFilters({
        department: nextPayload.selectedDepartment || '',
        year: nextPayload.selectedYear ? String(nextPayload.selectedYear) : '',
        semester: nextPayload.selectedSemester || '',
        test_name: nextPayload.selectedTestName || '',
        q: nextPayload.searchQuery || '',
        sort: nextPayload.sortMode || 'pending_first',
      });
    });
  }

  async function loadActivityOverview(filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
    q?: string;
    sort?: string;
  }, options?: { preferCache?: boolean }) {
    const normalizedFilters = {
      department: String(filters?.department || '').trim().toUpperCase(),
      year: Number(filters?.year || 0) || 0,
      semester: String(filters?.semester || '').trim(),
      test_name: String(filters?.test_name || '').trim(),
      q: String(filters?.q || '').trim(),
      sort: String(filters?.sort || '').trim() || 'pending_first',
    };
    const cacheKey = buildActivityOverviewCacheKey(normalizedFilters);
    const cached = options?.preferCache === false ? null : readOverviewCacheEntry(activityOverviewCacheRef, 'activity', cacheKey);
    if (cached) {
      applyActivityOverviewPayload(cached.payload);
      if (Date.now() - cached.timestamp < SCOPE_CACHE_TTL_MS) return;
    }
    setActivityLoading(!cached);
    try {
      const payload = await getActivityOverview({
        department: normalizedFilters.department || undefined,
        year: normalizedFilters.year || null,
        semester: normalizedFilters.semester || undefined,
        test_name: normalizedFilters.test_name || undefined,
        q: normalizedFilters.q || undefined,
        sort: normalizedFilters.sort,
      });
      writeOverviewCacheEntry(
        activityOverviewCacheRef,
        'activity',
        cacheKey,
        payload,
        shouldPersistActivityOverviewPayload(payload),
      );
      applyActivityOverviewPayload(payload);
    } catch (error) {
      setActivityData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load counselor activity.' });
    } finally {
      setActivityLoading(false);
    }
  }

  async function loadAdminMessages(filters?: {
    day?: string;
    q?: string;
    year?: string;
    month?: string;
    day_num?: string;
  }, limit = adminMessagesLimit) {
    setAdminMessagesLoading(true);
    try {
      const normalizedLimit = Math.max(100, limit || DEFAULT_ADMIN_MESSAGES_LIMIT);
      const payload = await getAdminMessagesOverview({ ...filters, limit: normalizedLimit });
      setAdminMessagesData(payload);
      setAdminMessagesLimit(normalizedLimit);
      setAdminMessageFilters({
        day: payload.filters.day || '',
        q: payload.filters.q || '',
        year: payload.filters.year || '',
        month: payload.filters.month || '',
        day_num: payload.filters.day_num || '',
      });
      setAdminMessageSearch(payload.filters.q || '');
      setSelectedAdminMessageIds([]);
    } catch (error) {
      setAdminMessagesData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load message logs.' });
    } finally {
      setAdminMessagesLoading(false);
    }
  }

  function reloadAdminMessages(filters?: {
    day?: string;
    q?: string;
    year?: string;
    month?: string;
    day_num?: string;
  }) {
    const nextLimit = DEFAULT_ADMIN_MESSAGES_LIMIT;
    setAdminMessagesLimit(nextLimit);
    return loadAdminMessages(filters, nextLimit);
  }

  async function loadMonitoringOverview() {
    setMonitoringLoading(true);
    try {
      const payload = await getMonitoringOverview();
      setMonitoringData(payload);
    } catch (error) {
      setMonitoringData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load session monitoring.' });
    } finally {
      setMonitoringLoading(false);
    }
  }

  async function loadDatabaseOverview() {
    setDatabaseLoading(true);
    try {
      const payload = await getDatabaseOverview();
      setDatabaseData(payload);
      setDatabaseBatchName(payload.currentBatchYear || '');
    } catch (error) {
      setDatabaseData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load database tools.' });
    } finally {
      setDatabaseLoading(false);
    }
  }

  function applyConfigPayload(payload: ConfigOverviewPayload) {
    setConfigData(payload);
    setEnvDraft(payload.envContent || '');
    setConfigPromptPassword('');
    setConfigPasswordPrompt(null);
    const nextConfigForm = {
      enable_counselor_batch_send: toBooleanString(payload.appConfig.enable_counselor_batch_send),
      counselor_batch_send_delay_seconds: payload.appConfig.counselor_batch_send_delay_seconds || '4',
      desktop_send_workspace_enabled: String(payload.appConfig.desktop_send_workspace_enabled || 'true').trim().toLowerCase() !== 'false',
      current_batch_year: payload.appConfig.current_batch_year || '',
      session_timeout_hours: String(Math.max(1, Math.round((Number(payload.appConfig.session_timeout || 86400) || 86400) / 3600))),
      session_heartbeat_interval: payload.appConfig.session_heartbeat_interval || '30',
      desktop_notification_poll_seconds: payload.appConfig.desktop_notification_poll_seconds || payload.appConfig.desktop_notification_poll_minutes || '30',
      notification_pending_threshold_days: payload.appConfig.notification_pending_threshold_days || '2',
      allow_concurrent_sessions: toBooleanString(payload.appConfig.allow_concurrent_sessions),
      max_concurrent_sessions: payload.appConfig.max_concurrent_sessions || '1',
      enable_periodic_backups: toBooleanString(payload.appConfig.enable_periodic_backups),
      periodic_backup_hour: payload.appConfig.periodic_backup_hour || '0',
      periodic_backup_minute: payload.appConfig.periodic_backup_minute || '0',
      disable_default_admin_on_new_system_admin: toBooleanString(payload.appConfig.disable_default_admin_on_new_system_admin),
      tutorial_master_enabled: toBooleanString(payload.appConfig.tutorial_master_enabled),
      tutorial_counselor_enabled: toBooleanString(payload.appConfig.tutorial_counselor_enabled),
      tutorial_hod_enabled: toBooleanString(payload.appConfig.tutorial_hod_enabled),
      tutorial_deo_enabled: toBooleanString(payload.appConfig.tutorial_deo_enabled),
      tutorial_principal_enabled: toBooleanString(payload.appConfig.tutorial_principal_enabled),
      require_otp_on_password_reset: toBooleanString(payload.appConfig.require_otp_on_password_reset),
      require_otp_on_login: toBooleanString(payload.appConfig.require_otp_on_login),
      otp_login_lock_hours: payload.appConfig.otp_login_lock_hours || '5',
      counselor_login_otp_enabled: toBooleanString(payload.appConfig.counselor_login_otp_enabled),
      notice_copy_as_image: toBooleanString(payload.appConfig.notice_copy_as_image),
      activity_copy_as_image: toBooleanString(payload.appConfig.activity_copy_as_image),
      notice_defaulter_copy_template: payload.appConfig.notice_defaulter_copy_template || DEFAULT_NOTICE_DEFAULTER_COPY_TEMPLATE,
      activity_defaulter_copy_template: payload.appConfig.activity_defaulter_copy_template || DEFAULT_ACTIVITY_DEFAULTER_COPY_TEMPLATE,
      cdp_defaulter_copy_template: payload.appConfig.cdp_defaulter_copy_template || DEFAULT_CDP_DEFAULTER_COPY_TEMPLATE,
      backup_storage_mode: payload.appConfig.backup_storage_mode || 'local',
      smtp_server: payload.appConfig.smtp_server || '',
      smtp_port: payload.appConfig.smtp_port || '587',
      smtp_username: payload.appConfig.smtp_username || '',
      smtp_password: '',
      email_from: payload.appConfig.email_from || '',
      google_oauth_enabled: toBooleanString(payload.appConfig.google_oauth_enabled),
      google_oauth_client_id: payload.appConfig.google_oauth_client_id || '',
      google_oauth_client_secret: '',
      google_oauth_allowed_domain: payload.appConfig.google_oauth_allowed_domain || '',
      google_oauth_redirect_base_url: payload.appConfig.google_oauth_redirect_base_url || '',
      google_oauth_bulk_password_mode: payload.appConfig.google_oauth_bulk_password_mode || 'sheet',
      google_oauth_bulk_override_password: '',
      google_drive_refresh_token: '',
      google_drive_folder_id: payload.appConfig.google_drive_folder_id || '',
    };
    setConfigForm(nextConfigForm);
    setConfigBaselineSnapshot(JSON.stringify(nextConfigForm));
  }

  async function loadConfigOverview() {
    setConfigLoading(true);
    try {
      const payload = await getConfigOverview();
      applyConfigPayload(payload);
    } catch (error) {
      setConfigData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load settings.' });
    } finally {
      setConfigLoading(false);
    }
  }

  async function loadServerConsole(limit = 30) {
    setServerConsoleLoading(true);
    try {
      const payload = await getServerConsole(limit);
      setServerConsoleData(payload);
    } catch (error) {
      setServerConsoleData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load server console.' });
    } finally {
      setServerConsoleLoading(false);
    }
  }

  async function loadTestDetail(testId: number) {
    setTestDetailLoading(true);
    try {
      if (currentUser?.role === 'counselor') {
        setActiveTab('test-database');
      }
      const payload = await getTestDetail(testId);
      setTestDetail(payload);
      testDetailOriginalMarksRef.current = buildTestDetailMarksSnapshot(payload);
      setTestMetaDraft({
        test_name: payload.meta.test_name || '',
        semester: payload.meta.semester || '',
        batch_name: payload.meta.batch_name || '',
        section: payload.meta.section || '',
      });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load test details.' });
    } finally {
      setTestDetailLoading(false);
    }
  }

  function stopCounselorBatchSend() {
    counselorBatchRunningRef.current = false;
    setCounselorBatchRunning(false);
    if (counselorBatchTimerRef.current) {
      window.clearTimeout(counselorBatchTimerRef.current);
      counselorBatchTimerRef.current = null;
    }
  }

  async function openCounselorSendPage(testId: number, mode: CounselorSendMode = 'app') {
    const resolvedMode = mode;
    setActiveTab('test-database');
    setCounselorSendVerify(null);
    setDesktopWhatsappWorkspaceStarted(false);
    setDesktopWhatsappActiveTarget(null);
    setDesktopReportQueueState({});
    setCounselorSendLoading(true);
    try {
      const payload = await getCounselorSendPage(testId, resolveCounselorSendBackendMode(resolvedMode));
      const defaultOrder = buildDefaultOrderList(payload.rows);
      let storedValues: Partial<typeof counselorSendVars> = {};
      try {
        storedValues = JSON.parse(localStorage.getItem(`send_common_vars_${payload.testId}`) || '{}');
      } catch {
        storedValues = {};
      }

      const nextVars = {
        test_name: String(storedValues.test_name || payload.meta.test_name || ''),
        semester: String(storedValues.semester || payload.meta.semester || ''),
        batch_name: String(storedValues.batch_name || payload.meta.batch_name || payload.defaultBatchName || ''),
        template: String(storedValues.template || DEFAULT_REPORT_TEMPLATE),
        sendMode: resolvedMode,
      };
      counselorSendVarsRef.current = nextVars;
      setCounselorSendPage(payload);
      setCounselorDefaultFieldOrder(defaultOrder.map((item) => ({ ...item })));
      setCounselorFieldOrder(defaultOrder.map((item) => ({ ...item })));
      setCounselorSendVars(nextVars);
      setCounselorBatchIndex(0);
      setCounselorBatchLastStudent('');
      setCounselorIncludeGenerated(false);
      counselorBatchIndexRef.current = 0;
      counselorBatchQueueRef.current = [];
      stopCounselorBatchSend();
      setTestDetail(null);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to open send results page.' });
    } finally {
      setCounselorSendLoading(false);
    }
  }

  function startCounselorSendFlow(testId: number, testName: string) {
    setSendResultOpeningId(testId);
    if (isMobileUi()) {
      void openCounselorSendPage(testId, 'app').finally(() => setSendResultOpeningId((current) => current === testId ? null : current));
      return;
    }

    if (embeddedWhatsappDesktopEnabled) {
      void (async () => {
        try {
          const availability = await getAvailableDesktopSendTargets();
          setDesktopWhatsappState((prev) => ({ ...prev, availableTargets: availability }));
          if (!availability.whatsapp_desktop) {
            setMissingWhatsappPrompt({ kind: 'report', id: testId, title: testName || 'Selected Test' });
            return;
          }
          setActiveTab('test-database');
          setTestDetail(null);
          setCounselorSendPage(null);
          setCounselorSendVerify(null);
          setDesktopWhatsappWorkspaceStarted(false);
          setDesktopWhatsappActiveTarget(null);
          setDesktopReportQueueState({});
          stopCounselorBatchSend();
          await openCounselorSendPage(testId, 'app');
        } catch (error) {
          setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Unable to check WhatsApp Desktop availability.' });
        } finally {
          setSendResultOpeningId((current) => current === testId ? null : current);
        }
      })();
      return;
    }

    setActiveTab('test-database');
    setTestDetail(null);
    setCounselorSendPage(null);
    setCounselorSendVerify(null);
    setDesktopWhatsappWorkspaceStarted(false);
    setDesktopWhatsappActiveTarget(null);
    setDesktopReportQueueState({});
    stopCounselorBatchSend();

    setCounselorSendVerify({
      testId,
      testName: testName || 'Selected Test',
      appFound: false,
      completed: false,
      tone: 'neutral',
      title: 'Checking...',
      body: 'Trying to open WhatsApp app using direct app link.',
    });
    setSendResultOpeningId((current) => current === testId ? null : current);
  }

  function installWhatsappAndReturn() {
    openExternalLink('ms-windows-store://pdp/?ProductId=9NKSQGP7F2NH');
    setActiveTab('recent-tests');
    setCounselorSendVerify(null);
  }

  function installWhatsappFromPrompt() {
    void openExternalLink('ms-windows-store://pdp/?ProductId=9NKSQGP7F2NH');
    setMissingWhatsappPrompt(null);
  }

  function useWhatsappWebFromPrompt() {
    const prompt = missingWhatsappPrompt;
    if (!prompt) return;
    setMissingWhatsappPrompt(null);
    if (prompt.kind === 'notice') {
      void openCounselorNoticeSendPage(prompt.id, 'web');
      return;
    }
    void openCounselorSendPage(prompt.id, 'web');
  }

  function stopCounselorNoticeBatchSend() {
    counselorNoticeBatchRunningRef.current = false;
    setCounselorNoticeBatchRunning(false);
    if (counselorNoticeBatchTimerRef.current) {
      window.clearTimeout(counselorNoticeBatchTimerRef.current);
      counselorNoticeBatchTimerRef.current = null;
    }
  }

  async function openCounselorNoticeSendPage(noticeId: number, mode: CounselorSendMode = 'app') {
    const resolvedMode = mode;
    setActiveTab('notices');
    setCounselorNoticeSendVerify(null);
    setDesktopWhatsappWorkspaceStarted(false);
    setDesktopWhatsappActiveTarget(null);
    setDesktopNoticeQueueState({});
    setCounselorNoticeSendLoading(true);
    try {
      const payload = await getCounselorNoticeSendPage(noticeId, resolveCounselorSendBackendMode(resolvedMode));
      let storedValues: Partial<typeof counselorNoticeSendVars> = {};
      try {
        storedValues = JSON.parse(localStorage.getItem(`notice_send_vars_${payload.noticeId}`) || '{}');
      } catch {
        storedValues = {};
      }

      const defaultTemplate = String(storedValues.template || payload.defaultTemplate || '');
      const nextVars = {
        title: String(storedValues.title || payload.notice.title || ''),
        text: String(storedValues.text || payload.notice.message_text || ''),
        template: defaultTemplate,
        sendMode: resolvedMode,
      };
      counselorNoticeSendVarsRef.current = nextVars;
      setCounselorNoticeSendPage(payload);
      setCounselorNoticeSendVars(nextVars);
      setCounselorNoticeAutoTemplate(payload.defaultTemplate || '');
      setCounselorNoticeTemplateEdited(Boolean(storedValues.template && storedValues.template !== payload.defaultTemplate));
      setCounselorNoticeBatchIndex(0);
      setCounselorNoticeBatchLastStudent('');
      setCounselorNoticeIncludeGenerated(false);
      counselorNoticeBatchIndexRef.current = 0;
      counselorNoticeBatchQueueRef.current = [];
      stopCounselorNoticeBatchSend();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to open send notice page.' });
    } finally {
      setCounselorNoticeSendLoading(false);
    }
  }

  function startCounselorNoticeSendFlow(notice: NoticeRecord) {
    setSendNoticeOpeningId(notice.id);
    if (isMobileUi()) {
      void openCounselorNoticeSendPage(notice.id, 'app').finally(() => setSendNoticeOpeningId((current) => current === notice.id ? null : current));
      return;
    }

    if (embeddedWhatsappDesktopEnabled) {
      void (async () => {
        try {
          const availability = await getAvailableDesktopSendTargets();
          setDesktopWhatsappState((prev) => ({ ...prev, availableTargets: availability }));
          if (!availability.whatsapp_desktop) {
            setMissingWhatsappPrompt({ kind: 'notice', id: notice.id, title: notice.title_display || notice.title || 'Selected Notice' });
            return;
          }
          setActiveTab('notices');
          setCounselorNoticeSendPage(null);
          setCounselorNoticeSendVerify(null);
          setDesktopWhatsappWorkspaceStarted(false);
          setDesktopWhatsappActiveTarget(null);
          setDesktopNoticeQueueState({});
          stopCounselorNoticeBatchSend();
          await openCounselorNoticeSendPage(notice.id, 'app');
        } catch (error) {
          setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Unable to check WhatsApp Desktop availability.' });
        } finally {
          setSendNoticeOpeningId((current) => current === notice.id ? null : current);
        }
      })();
      return;
    }

    setActiveTab('notices');
    setCounselorNoticeSendPage(null);
    setCounselorNoticeSendVerify(null);
    setDesktopWhatsappWorkspaceStarted(false);
    setDesktopWhatsappActiveTarget(null);
    setDesktopNoticeQueueState({});
    stopCounselorNoticeBatchSend();

    setCounselorNoticeSendVerify({
      noticeId: notice.id,
      noticeTitle: notice.title_display || notice.title || 'Selected Notice',
      appFound: false,
      completed: false,
      tone: 'neutral',
      title: 'Checking...',
      body: 'Trying to open WhatsApp app using direct app link.',
    });
    setSendNoticeOpeningId((current) => current === notice.id ? null : current);
  }

  function installWhatsappForNoticeAndReturn() {
    openExternalLink('ms-windows-store://pdp/?ProductId=9NKSQGP7F2NH');
    setActiveTab('notices');
    setCounselorNoticeSendVerify(null);
  }

  function markCounselorRowGenerated(regNo: string) {
    setCounselorSendPage((prev) => {
      if (!prev) return prev;
      return {
        ...prev,
        rows: prev.rows.map((row) => (row.reg_no === regNo ? { ...row, status: 'Generated' } : row)),
      };
    });
  }

  function getOrderedFieldPayload() {
    return counselorFieldOrder.map((entry) =>
      entry.type === 'subject'
        ? { type: 'subject', raw_key: entry.rawKey, normalized_key: entry.normalizedKey }
        : { type: 'metric', key: entry.metricKey, normalized_key: entry.metricKey },
    );
  }

  function buildSendFormData(row: CounselorSendReportRow, step: 'prepare' | 'confirm', extra: Record<string, string> = {}) {
    if (!counselorSendPage) throw new Error('Send page is not loaded.');
    const formData = new FormData();
    formData.set('test_id', String(counselorSendPage.testId));
    formData.set('reg_no', row.reg_no);
    formData.set('action', 'send');
    formData.set('step', step);
    formData.set('message_template', counselorSendVarsRef.current.template || '');
    formData.set('test_name', counselorSendVarsRef.current.test_name || '');
    formData.set('semester', counselorSendVarsRef.current.semester || '');
    formData.set('batch_name', counselorSendVarsRef.current.batch_name || '');
    formData.set('section', counselorSendPage.meta.section || '');
    formData.set('department', row.department || counselorSendPage.meta.department || '');
    formData.set('ordered_fields', JSON.stringify(getOrderedFieldPayload()));
    formData.set('send_mode', isMobileUi() ? 'app' : resolveCounselorSendBackendMode(counselorSendVarsRef.current.sendMode));
    for (const [key, value] of Object.entries(extra)) {
      formData.set(key, value);
    }
    return formData;
  }

  function getDesktopWorkspaceTargetPreference() {
    return getDesktopWorkspaceLaunchTarget();
  }

  function scrollDesktopWorkspaceIntoView(kind: 'report' | 'notice') {
    window.requestAnimationFrame(() => {
      window.requestAnimationFrame(() => {
        const queueShell = kind === 'report' ? desktopReportQueueShellRef.current : desktopNoticeQueueShellRef.current;
        contentAreaRef.current?.scrollTo({ top: 0, left: 0, behavior: 'auto' });
        mainContentRef.current?.scrollTo({ top: 0, left: 0, behavior: 'auto' });
        window.scrollTo({ top: 0, left: 0, behavior: 'auto' });
        if (queueShell) {
          queueShell.scrollTo({ top: 0, left: 0, behavior: 'auto' });
        }
      });
    });
  }

  async function runDesktopWorkspaceTransition<T>(
    phase: 'enter' | 'exit',
    action: () => Promise<T>,
  ) {
    setDesktopWhatsappWorkspaceTransition(phase);
    await new Promise<void>((resolve) => {
      window.requestAnimationFrame(() => {
        window.requestAnimationFrame(() => {
          resolve();
        });
      });
    });
    const startedAt = typeof performance !== 'undefined' ? performance.now() : Date.now();
    try {
      return await action();
    } finally {
      const now = typeof performance !== 'undefined' ? performance.now() : Date.now();
      const remaining = Math.max(0, 260 - (now - startedAt));
      if (remaining > 0) {
        await new Promise((resolve) => window.setTimeout(resolve, remaining));
      }
      await new Promise<void>((resolve) => {
        window.requestAnimationFrame(() => {
          window.requestAnimationFrame(() => {
            setDesktopWhatsappWorkspaceTransition(null);
            resolve();
          });
        });
      });
    }
  }

  async function startDesktopWhatsappWorkspace(kind: 'report' | 'notice') {
    if (!embeddedWhatsappDesktopFlowEnabled) return false;
    const sendMode = kind === 'report' ? counselorSendVarsRef.current.sendMode : counselorNoticeSendVarsRef.current.sendMode;
    if (kind === 'report') {
      setCounselorSendVars((prev) => ({ ...prev, ...counselorSendVarsRef.current }));
    } else {
      setCounselorNoticeSendVars((prev) => ({ ...prev, ...counselorNoticeSendVarsRef.current }));
    }
    setDesktopWhatsappWorkspaceBusy(true);
    setDesktopWhatsappWorkspaceExiting(false);
    setDesktopWhatsappActiveTarget(null);
    setDesktopWhatsappLoadingRow(null);
    try {
      const preopened = await preopenDesktopSendTarget(sendMode);
      setDesktopWhatsappWorkspaceReady(true);
      setDesktopWhatsappWorkspaceStarted(true);
      setDesktopWhatsappState((prev) => ({
        ...prev,
        supported: true,
        active: true,
        loading: false,
        preferredTarget: preopened?.target || getDesktopWorkspaceTargetPreference(),
        preferredTargetLabel: preopened?.label || (sendMode === 'web' ? 'Google Chrome' : 'WhatsApp Desktop'),
        error: '',
      }));
      scrollDesktopWorkspaceIntoView(kind);
      return true;
    } catch (error) {
      setDesktopWhatsappWorkspaceReady(false);
      setDesktopWhatsappWorkspaceStarted(false);
      setDesktopWhatsappState((prev) => ({
        ...prev,
        active: false,
        loading: false,
        error: error instanceof Error ? error.message : 'Unable to open WhatsApp before starting workflow.',
      }));
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Unable to open WhatsApp before starting workflow.' });
      return false;
    } finally {
      setDesktopWhatsappWorkspaceBusy(false);
    }
  }

  async function hideDesktopWhatsappWorkspace() {
    return runDesktopWorkspaceTransition('exit', async () => {
      const activeKind = desktopWhatsappActiveTarget?.kind || (counselorSendPage ? 'report' : 'notice');
      setDesktopWhatsappWorkspaceExiting(true);
      await new Promise((resolve) => window.setTimeout(resolve, 180));
      setDesktopWhatsappWorkspaceStarted(false);
      setDesktopWhatsappActiveTarget(null);
      setDesktopWhatsappState(await hideDesktopSendWorkspace(getDesktopWorkspaceTargetPreference()));
      scrollDesktopWorkspaceIntoView(activeKind);
      setDesktopWhatsappWorkspaceExiting(false);
    });
  }

  async function stopDesktopWhatsappWorkspaceImmediate() {
    setDesktopWhatsappWorkspaceBusy(true);
    try {
      setDesktopWhatsappWorkspaceExiting(false);
      setDesktopWhatsappWorkspaceReady(false);
      setDesktopWhatsappWorkspaceStarted(false);
      setDesktopWhatsappActiveTarget(null);
      setDesktopWhatsappLoadingRow(null);
      setDesktopWhatsappState(await exitDesktopSendWorkspace(getDesktopWorkspaceTargetPreference()));
    } finally {
      setDesktopWhatsappWorkspaceBusy(false);
    }
  }

  async function stopDesktopWhatsappWorkspace() {
    return runDesktopWorkspaceTransition('exit', async () => {
      await stopDesktopWhatsappWorkspaceImmediate();
    });
  }

  async function handleCounselorSendModeChange(nextMode: CounselorSendMode) {
    if (nextMode !== 'app' && desktopWhatsappWorkspaceReady) {
      await stopDesktopWhatsappWorkspaceImmediate();
    }
    counselorSendVarsRef.current = { ...counselorSendVarsRef.current, sendMode: nextMode };
    setCounselorSendVars((prev) => ({ ...prev, sendMode: nextMode }));
  }

  async function handleCounselorNoticeSendModeChange(nextMode: CounselorSendMode) {
    if (nextMode !== 'app' && desktopWhatsappWorkspaceReady) {
      await stopDesktopWhatsappWorkspaceImmediate();
    }
    counselorNoticeSendVarsRef.current = { ...counselorNoticeSendVarsRef.current, sendMode: nextMode };
    setCounselorNoticeSendVars((prev) => ({ ...prev, sendMode: nextMode }));
  }

  async function openPreparedDesktopTarget(rawLink: string, mode: CounselorSendMode = 'app') {
    const appLink = resolveWaLinkByMode(rawLink, 'app');
    const webLink = resolveWaLinkByMode(rawLink, 'web');
    const targetPreference: DesktopSendTargetPreference = mode === 'web' ? 'chrome' : getDesktopWorkspaceTargetPreference();
    const result = await openExternalSendTarget({
      preference: targetPreference,
      appUrl: appLink,
      webUrl: webLink,
      reuseBrowserSession: mode === 'web',
    });
    setDesktopWhatsappState((prev) => ({
      ...prev,
      preferredTarget: result.target,
      preferredTargetLabel: result.label,
      availableTargets: result.availability,
      error: result.error || '',
    }));
    if (!result.success) {
      throw new Error(result.error || 'No supported external send target could be opened.');
    }
    return result;
  }

  async function preopenDesktopSendTarget(mode: CounselorSendMode) {
    if (mode !== 'app' && mode !== 'web') return null;
    const verificationWebLink = WHATSAPP_VERIFICATION_WEB_LINK;
    const resolvedVerificationAppLink = resolveWaLinkByMode(verificationWebLink, 'app');
    const verificationAppLink = /^whatsapp:\/\//i.test(resolvedVerificationAppLink) ? resolvedVerificationAppLink : 'whatsapp://send';
    if (mode === 'app') {
      void openExternalLink(verificationAppLink || 'whatsapp://send');
      return {
        success: true,
        target: 'whatsapp_desktop' as DesktopSendTargetPreference,
        label: 'WhatsApp Desktop',
        availability: desktopWhatsappState.availableTargets,
      };
    }
    const result = await openExternalSendTarget({
      preference: 'chrome',
      appUrl: verificationAppLink || 'whatsapp://send',
      webUrl: verificationWebLink,
      reuseBrowserSession: true,
    });
    setDesktopWhatsappState((prev) => ({
      ...prev,
      preferredTarget: result.target,
      preferredTargetLabel: result.label,
      availableTargets: result.availability,
      error: result.error || '',
    }));
    if (!result.success) {
      throw new Error(result.error || 'No supported WhatsApp target could be opened.');
    }
    await new Promise((resolve) => window.setTimeout(resolve, 250));
    return result;
  }

  async function prepareSingleCounselorDelivery(row: CounselorSendReportRow) {
    const payload = await sendSingleReport(buildSendFormData(row, 'prepare'));
    return {
      deliveryToken: String(payload.delivery_token || ''),
      waLink: String(payload.wa_link || ''),
    };
  }

  async function confirmSingleCounselorDelivery(row: CounselorSendReportRow, deliveryToken: string, outcome: 'sent' | 'failed' | 'skipped') {
    await sendSingleReport(
      buildSendFormData(row, 'confirm', {
        delivery_token: deliveryToken,
        delivery_outcome: outcome,
      }),
    );
  }

  function setDesktopReportRowState(regNo: string, state: DesktopSendQueueState) {
    setDesktopReportQueueState((prev) => ({ ...prev, [regNo]: state }));
  }

  async function handleCounselorSendSingle(row: CounselorSendReportRow) {
    const currentSendPage = counselorSendPage;
    if (!currentSendPage) return false;
    try {
      const prepared = await prepareSingleCounselorDelivery(row);
      if (!prepared.waLink) {
        throw new Error('Parent phone number is missing or invalid for this student.');
      }

      const effectiveSendMode: CounselorSendMode = isMobileUi() ? 'app' : counselorSendVarsRef.current.sendMode;
      if ((effectiveSendMode === 'app' || effectiveSendMode === 'web' || effectiveSendMode === 'embed') && embeddedWhatsappDesktopFlowEnabled && desktopWhatsappWorkspaceStarted) {
        setDesktopWhatsappActiveTarget({
          kind: 'report',
          regNo: row.reg_no,
          studentName: row.student_name,
          deliveryToken: prepared.deliveryToken,
          waLink: prepared.waLink,
        });
        setDesktopReportRowState(row.reg_no, 'opened');
        await openPreparedDesktopTarget(prepared.waLink, effectiveSendMode);
        await confirmSingleCounselorDelivery(row, prepared.deliveryToken, 'sent');
        markCounselorRowGenerated(row.reg_no);
        setDesktopReportRowState(row.reg_no, 'sent');
        return true;
      }
      if (effectiveSendMode === 'web' || effectiveSendMode === 'embed') {
        if (effectiveSendMode === 'embed' && embeddedWhatsappDesktopFlowEnabled) {
          if (!desktopWhatsappWorkspaceStarted) {
            throw new Error('Start the desktop workspace before selecting a student.');
          }
          setDesktopWhatsappActiveTarget({
            kind: 'report',
            regNo: row.reg_no,
            studentName: row.student_name,
            deliveryToken: prepared.deliveryToken,
            waLink: prepared.waLink,
          });
          setDesktopReportRowState(row.reg_no, 'opened');
          await openPreparedDesktopTarget(prepared.waLink);
          await confirmSingleCounselorDelivery(row, prepared.deliveryToken, 'sent');
          markCounselorRowGenerated(row.reg_no);
          setDesktopReportRowState(row.reg_no, 'sent');
          return true;
        } else {
          saveSendReturnState({
            kind: 'report',
            id: currentSendPage.testId,
            mode: 'web',
            timestamp: Date.now(),
          });
          if (!openWhatsAppWebDirect(prepared.waLink)) {
            throw new Error('Unable to open WhatsApp Web link.');
          }
        }
        await confirmSingleCounselorDelivery(row, prepared.deliveryToken, 'sent');
        markCounselorRowGenerated(row.reg_no);
        return true;
      }

      if (!openWhatsAppAppDirect(prepared.waLink)) {
        throw new Error('Unable to open WhatsApp app link for this parent number.');
      }
      await confirmSingleCounselorDelivery(row, prepared.deliveryToken, 'sent');
      markCounselorRowGenerated(row.reg_no);
      return true;
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : `Unable to send for ${row.reg_no}.` });
      return false;
    }
  }

  async function confirmDesktopReportDelivery(outcome: 'sent' | 'failed' | 'skipped') {
    const activeTarget = desktopWhatsappActiveTarget;
    const currentPage = counselorSendPage;
    if (!activeTarget || activeTarget.kind !== 'report' || !currentPage) return;
    const row = currentPage.rows.find((item) => item.reg_no === activeTarget.regNo);
    if (!row) return;
    try {
      await confirmSingleCounselorDelivery(row, activeTarget.deliveryToken, outcome);
      if (outcome === 'sent') {
        markCounselorRowGenerated(activeTarget.regNo);
        setDesktopReportRowState(activeTarget.regNo, 'sent');
      } else {
        setDesktopReportRowState(activeTarget.regNo, outcome);
      }
      setDesktopWhatsappActiveTarget(null);
      if (outcome === 'sent') {
        setFlash({ type: 'success', message: `Marked ${activeTarget.studentName} as sent.` });
      } else if (outcome === 'failed') {
        setFlash({ type: 'warning', message: `Marked ${activeTarget.studentName} as failed. You can reopen the message anytime.` });
      } else {
        setFlash({ type: 'info', message: `Skipped ${activeTarget.studentName} for now.` });
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to update delivery state.' });
    }
  }

  function moveToNextDesktopReportRow() {
    const currentPage = counselorSendPage;
    if (!currentPage) return;
    const nextRow = currentPage.rows.find((row) => row.status !== 'Generated' && row.reg_no !== desktopWhatsappActiveTarget?.regNo);
    if (nextRow) {
      void handleCounselorSendSingle(nextRow);
    } else {
      setFlash({ type: 'info', message: 'No more pending students in this queue.' });
    }
  }

  function moveCounselorFieldOrder(index: number, direction: -1 | 1) {
    setCounselorFieldOrder((prev) => {
      const target = index + direction;
      if (target < 0 || target >= prev.length) return prev;
      const next = [...prev];
      const temp = next[index];
      next[index] = next[target];
      next[target] = temp;
      return next;
    });
  }

  async function processNextCounselorBatchItem() {
    if (!counselorBatchRunningRef.current) return;
    if (counselorBatchIndexRef.current >= counselorBatchQueueRef.current.length) {
      stopCounselorBatchSend();
      setCounselorBatchIndex(0);
      counselorBatchIndexRef.current = 0;
      counselorBatchQueueRef.current = [];
      setCounselorBatchLastStudent('');
      setFlash({ type: 'success', message: 'Batch send completed.' });
      return;
    }

    const row = counselorBatchQueueRef.current[counselorBatchIndexRef.current];
    const success = await handleCounselorSendSingle(row);
    setCounselorBatchLastStudent(`${row.student_name} (${row.reg_no})`);
    if (!success) {
      stopCounselorBatchSend();
      return;
    }

    counselorBatchIndexRef.current += 1;
    setCounselorBatchIndex(counselorBatchIndexRef.current);
    if (counselorBatchRunningRef.current) {
      counselorBatchTimerRef.current = window.setTimeout(
        () => void processNextCounselorBatchItem(),
        Math.max(1000, (counselorSendPage?.batchSendDelaySeconds || 4) * 1000),
      );
    }
  }

  async function startCounselorBatchSend() {
    if (!counselorSendPage) return;
    if (embeddedWhatsappDesktopFlowEnabled) {
      setFlash({ type: 'info', message: 'Desktop send workspace uses one-at-a-time sending only. Batch send is disabled here.' });
      return;
    }
    const queue = counselorSendPage.rows.filter((row) => counselorIncludeGenerated || row.status !== 'Generated');
    if (!queue.length) {
      setFlash({ type: 'warning', message: 'No students found to batch send.' });
      return;
    }

    if (counselorBatchIndexRef.current === 0) {
      const confirmed = await requestConfirm({
        title: 'Start Batch Send',
        message: `Start batch send for ${queue.length} students?`,
        confirmLabel: 'Start',
        confirmClassName: 'btn btn-primary btn-sm',
        iconClassName: 'fas fa-paper-plane',
      });
      if (!confirmed) return;
      counselorBatchQueueRef.current = queue;
    }

    counselorBatchRunningRef.current = true;
    setCounselorBatchRunning(true);
    void processNextCounselorBatchItem();
  }

  async function handleCounselorDesktopQueuePick(row: CounselorSendReportRow) {
    setDesktopWhatsappLoadingRow(row.reg_no);
    if (!desktopWhatsappWorkspaceStarted) {
      const started = await startDesktopWhatsappWorkspace('report');
      if (!started) {
        setDesktopWhatsappLoadingRow(null);
        return;
      }
    }
    try {
      await handleCounselorSendSingle(row);
    } finally {
      setDesktopWhatsappLoadingRow(null);
    }
  }

  function markCounselorNoticeRowGenerated(regNo: string) {
    setCounselorNoticeSendPage((prev) => {
      if (!prev) return prev;
      return {
        ...prev,
        rows: prev.rows.map((row) => (row.reg_no === regNo ? { ...row, status: 'Generated' } : row)),
      };
    });
  }

  function buildNoticeSendFormData(row: CounselorSendNoticeRow, step: 'prepare' | 'confirm', extra: Record<string, string> = {}) {
    if (!counselorNoticeSendPage) throw new Error('Notice send page is not loaded.');
    const formData = new FormData();
    formData.set('notice_id', String(counselorNoticeSendPage.noticeId));
    formData.set('reg_no', row.reg_no);
    formData.set('action', 'send');
    formData.set('step', step);
    formData.set('message_template', counselorNoticeSendVarsRef.current.template || '');
    formData.set('notice_title', counselorNoticeSendVarsRef.current.title || '');
    formData.set('notice_text', counselorNoticeSendVarsRef.current.text || '');
    formData.set('send_mode', isMobileUi() ? 'app' : resolveCounselorSendBackendMode(counselorNoticeSendVarsRef.current.sendMode));
    for (const [key, value] of Object.entries(extra)) {
      formData.set(key, value);
    }
    return formData;
  }

  async function prepareSingleCounselorNoticeDelivery(row: CounselorSendNoticeRow) {
    const payload = await sendSingleNotice(buildNoticeSendFormData(row, 'prepare'));
    return {
      deliveryToken: String(payload.delivery_token || ''),
      waLink: String(payload.wa_link || ''),
    };
  }

  async function confirmSingleCounselorNoticeDelivery(row: CounselorSendNoticeRow, deliveryToken: string, outcome: 'sent' | 'failed' | 'skipped') {
    await sendSingleNotice(
      buildNoticeSendFormData(row, 'confirm', {
        delivery_token: deliveryToken,
        delivery_outcome: outcome,
      }),
    );
  }

  function setDesktopNoticeRowState(regNo: string, state: DesktopSendQueueState) {
    setDesktopNoticeQueueState((prev) => ({ ...prev, [regNo]: state }));
  }

  async function handleCounselorNoticeSendSingle(row: CounselorSendNoticeRow) {
    const currentSendPage = counselorNoticeSendPage;
    if (!currentSendPage) return false;
    try {
      const prepared = await prepareSingleCounselorNoticeDelivery(row);
      if (!prepared.waLink) {
        throw new Error('Parent phone number is missing or invalid for this student.');
      }

      const effectiveSendMode: CounselorSendMode = isMobileUi() ? 'app' : counselorNoticeSendVarsRef.current.sendMode;
      if ((effectiveSendMode === 'app' || effectiveSendMode === 'web' || effectiveSendMode === 'embed') && embeddedWhatsappDesktopFlowEnabled && desktopWhatsappWorkspaceStarted) {
        setDesktopWhatsappActiveTarget({
          kind: 'notice',
          regNo: row.reg_no,
          studentName: row.student_name,
          deliveryToken: prepared.deliveryToken,
          waLink: prepared.waLink,
        });
        setDesktopNoticeRowState(row.reg_no, 'opened');
        await openPreparedDesktopTarget(prepared.waLink, effectiveSendMode);
        await confirmSingleCounselorNoticeDelivery(row, prepared.deliveryToken, 'sent');
        markCounselorNoticeRowGenerated(row.reg_no);
        setDesktopNoticeRowState(row.reg_no, 'sent');
        return true;
      }
      if (effectiveSendMode === 'web' || effectiveSendMode === 'embed') {
        if (effectiveSendMode === 'embed' && embeddedWhatsappDesktopFlowEnabled) {
          if (!desktopWhatsappWorkspaceStarted) {
            throw new Error('Start the desktop workspace before selecting a student.');
          }
          setDesktopWhatsappActiveTarget({
            kind: 'notice',
            regNo: row.reg_no,
            studentName: row.student_name,
            deliveryToken: prepared.deliveryToken,
            waLink: prepared.waLink,
          });
          setDesktopNoticeRowState(row.reg_no, 'opened');
          await openPreparedDesktopTarget(prepared.waLink);
          await confirmSingleCounselorNoticeDelivery(row, prepared.deliveryToken, 'sent');
          markCounselorNoticeRowGenerated(row.reg_no);
          setDesktopNoticeRowState(row.reg_no, 'sent');
          return true;
        } else {
          saveSendReturnState({
            kind: 'notice',
            id: currentSendPage.noticeId,
            mode: 'web',
            timestamp: Date.now(),
          });
          if (!openWhatsAppWebDirect(prepared.waLink)) {
            throw new Error('Unable to open WhatsApp Web link.');
          }
        }
        await confirmSingleCounselorNoticeDelivery(row, prepared.deliveryToken, 'sent');
        markCounselorNoticeRowGenerated(row.reg_no);
        return true;
      }

      if (!openWhatsAppAppDirect(prepared.waLink)) {
        throw new Error('Unable to open WhatsApp app link for this parent number.');
      }
      await confirmSingleCounselorNoticeDelivery(row, prepared.deliveryToken, 'sent');
      markCounselorNoticeRowGenerated(row.reg_no);
      return true;
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : `Unable to send notice for ${row.reg_no}.` });
      return false;
    }
  }

  async function confirmDesktopNoticeDelivery(outcome: 'sent' | 'failed' | 'skipped') {
    const activeTarget = desktopWhatsappActiveTarget;
    const currentPage = counselorNoticeSendPage;
    if (!activeTarget || activeTarget.kind !== 'notice' || !currentPage) return;
    const row = currentPage.rows.find((item) => item.reg_no === activeTarget.regNo);
    if (!row) return;
    try {
      await confirmSingleCounselorNoticeDelivery(row, activeTarget.deliveryToken, outcome);
      if (outcome === 'sent') {
        markCounselorNoticeRowGenerated(activeTarget.regNo);
        setDesktopNoticeRowState(activeTarget.regNo, 'sent');
      } else {
        setDesktopNoticeRowState(activeTarget.regNo, outcome);
      }
      setDesktopWhatsappActiveTarget(null);
      if (outcome === 'sent') {
        setFlash({ type: 'success', message: `Marked ${activeTarget.studentName} as sent.` });
      } else if (outcome === 'failed') {
        setFlash({ type: 'warning', message: `Marked ${activeTarget.studentName} as failed. You can reopen the message anytime.` });
      } else {
        setFlash({ type: 'info', message: `Skipped ${activeTarget.studentName} for now.` });
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to update delivery state.' });
    }
  }

  async function reopenDesktopActiveTarget() {
    const activeTarget = desktopWhatsappActiveTarget;
    if (!activeTarget?.waLink) return;
    try {
      await openPreparedDesktopTarget(activeTarget.waLink);
      setFlash({ type: 'info', message: `Reopened ${activeTarget.studentName} in ${desktopWhatsappState.preferredTargetLabel || 'the selected send target'}.` });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Unable to reopen the selected send target.' });
    }
  }

  function moveToNextDesktopNoticeRow() {
    const currentPage = counselorNoticeSendPage;
    if (!currentPage) return;
    const nextRow = currentPage.rows.find((row) => row.status !== 'Generated' && row.reg_no !== desktopWhatsappActiveTarget?.regNo);
    if (nextRow) {
      void handleCounselorNoticeSendSingle(nextRow);
    } else {
      setFlash({ type: 'info', message: 'No more pending students in this queue.' });
    }
  }

  async function processNextCounselorNoticeBatchItem() {
    if (!counselorNoticeBatchRunningRef.current) return;
    if (counselorNoticeBatchIndexRef.current >= counselorNoticeBatchQueueRef.current.length) {
      stopCounselorNoticeBatchSend();
      setCounselorNoticeBatchIndex(0);
      counselorNoticeBatchIndexRef.current = 0;
      counselorNoticeBatchQueueRef.current = [];
      setCounselorNoticeBatchLastStudent('');
      setFlash({ type: 'success', message: 'Notice batch send completed.' });
      return;
    }

    const row = counselorNoticeBatchQueueRef.current[counselorNoticeBatchIndexRef.current];
    const success = await handleCounselorNoticeSendSingle(row);
    setCounselorNoticeBatchLastStudent(`${row.student_name} (${row.reg_no})`);
    if (!success) {
      stopCounselorNoticeBatchSend();
      return;
    }

    counselorNoticeBatchIndexRef.current += 1;
    setCounselorNoticeBatchIndex(counselorNoticeBatchIndexRef.current);
    if (counselorNoticeBatchRunningRef.current) {
      counselorNoticeBatchTimerRef.current = window.setTimeout(
        () => void processNextCounselorNoticeBatchItem(),
        Math.max(1000, (counselorNoticeSendPage?.batchSendDelaySeconds || 4) * 1000),
      );
    }
  }

  async function startCounselorNoticeBatchSend() {
    if (!counselorNoticeSendPage) return;
    if (embeddedWhatsappDesktopFlowEnabled) {
      setFlash({ type: 'info', message: 'Desktop send workspace uses one-at-a-time sending only. Batch send is disabled here.' });
      return;
    }
    const queue = counselorNoticeSendPage.rows.filter((row) => counselorNoticeIncludeGenerated || row.status !== 'Generated');
    if (!queue.length) {
      setFlash({ type: 'warning', message: 'No students found to batch send.' });
      return;
    }

    if (counselorNoticeBatchIndexRef.current === 0) {
      const confirmed = await requestConfirm({
        title: 'Start Batch Send',
        message: `Start batch send for ${queue.length} students?`,
        confirmLabel: 'Start',
        confirmClassName: 'btn btn-primary btn-sm',
        iconClassName: 'fas fa-paper-plane',
      });
      if (!confirmed) return;
      counselorNoticeBatchQueueRef.current = queue;
    }

    counselorNoticeBatchRunningRef.current = true;
    setCounselorNoticeBatchRunning(true);
    void processNextCounselorNoticeBatchItem();
  }

  async function handleCounselorNoticeDesktopQueuePick(row: CounselorSendNoticeRow) {
    setDesktopWhatsappLoadingRow(row.reg_no);
    if (!desktopWhatsappWorkspaceStarted) {
      const started = await startDesktopWhatsappWorkspace('notice');
      if (!started) {
        setDesktopWhatsappLoadingRow(null);
        return;
      }
    }
    try {
      await handleCounselorNoticeSendSingle(row);
    } finally {
      setDesktopWhatsappLoadingRow(null);
    }
  }

  function updateLocalMark(regNo: string, subject: string, value: string) {
    setTestDetail((prev) => {
      if (!prev) return prev;
      return {
        ...prev,
        students: prev.students.map((student) =>
          student.reg_no === regNo
            ? { ...student, marks: { ...student.marks, [subject]: value } }
            : student,
        ),
      };
    });
  }

  function isTestDetailRowDirty(regNo: string) {
    if (!testDetail) return false;
    const student = testDetail.students.find((item) => item.reg_no === regNo);
    if (!student) return false;
    const baseline = testDetailOriginalMarksRef.current[regNo] || {};
    return testDetail.subjects.some((subject) => String(student.marks[subject] || '').trim() !== String(baseline[subject] || '').trim());
  }

  async function handleSaveMeta(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!testDetail) return;
    const nextTestName = String(testMetaDraft.test_name || testDetail.meta.test_name || '').trim().toUpperCase();
    const nextSemester = String(testMetaDraft.semester || testDetail.meta.semester || '').trim();
    const nextBatchName = String(testMetaDraft.batch_name || testDetail.meta.batch_name || '').trim();
    const conflictingTest = (reportsData?.tests || []).find((entry) =>
      entry.id !== testDetail.testId
      && String(entry.department || '').trim().toUpperCase() === String(testDetail.meta.department || '').trim().toUpperCase()
      && Number(entry.year_level || 1) === Number(testDetail.meta.year_level || 1)
      && String(entry.test_name || '').trim().toUpperCase() === nextTestName
      && String(entry.semester || '').trim() === nextSemester
      && String(entry.batch_name || '').trim().toLowerCase() === nextBatchName.toLowerCase(),
    );
    let overwriteExisting = false;
    if (conflictingTest) {
      const confirmed = await requestConfirm({
        title: 'Overwrite Existing Test',
        message: `This will overwrite the existing ${nextTestName} in Semester ${nextSemester}. Continue?`,
        confirmLabel: 'Overwrite',
        confirmClassName: 'btn btn-danger btn-sm',
        iconClassName: 'fas fa-triangle-exclamation',
      });
      if (!confirmed) return;
      overwriteExisting = true;
    }
    setSavingMeta(true);
    try {
      await saveTestMeta(testDetail.testId, {
        ...testMetaDraft,
        overwrite_existing: overwriteExisting,
      });
      invalidateOverviewCaches(['reports', 'dashboard', 'activity', 'activity-scope']);
      setFlash({ type: 'success', message: overwriteExisting ? 'Test metadata updated and existing target test overwritten successfully.' : 'Test metadata updated successfully.' });
      await loadTestDetail(testDetail.testId);
      if (reportsData?.selectedDepartment && reportsData.selectedYear) {
        await loadReports(reportsData.selectedDepartment, reportsData.selectedYear, { preferCache: false });
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to update test metadata.' });
    } finally {
      setSavingMeta(false);
    }
  }

  async function handleSaveRowMarks(regNo: string) {
    if (!testDetail) return;
    const student = testDetail.students.find((item) => item.reg_no === regNo);
    if (!student) return;
    try {
      await saveTestMarks(testDetail.testId, {
        reg_no: regNo,
        marks: Object.fromEntries(testDetail.subjects.map((subject) => [subject, student.marks[subject] || ''])),
      });
      testDetailOriginalMarksRef.current[regNo] = Object.fromEntries(
        testDetail.subjects.map((subject) => [subject, String(student.marks[subject] || '').trim()]),
      );
      invalidateOverviewCaches(['dashboard', 'activity', 'activity-scope']);
      setFlash({ type: 'success', message: `Marks updated for ${regNo}.` });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : `Failed to update ${regNo}.` });
    }
  }

  async function handleSaveAllMarks() {
    if (!testDetail || !testDetail.students.length) return;
    const confirmed = await requestConfirm({
      title: 'Save Marks',
      message: `Save marks for all ${testDetail.students.length} students?`,
      confirmLabel: 'Save',
      confirmClassName: 'btn btn-primary btn-sm',
      iconClassName: 'fas fa-save',
    });
    if (!confirmed) return;
    setSavingMarks(true);
    let successCount = 0;
    let failCount = 0;
    const savedRegNos: string[] = [];
    for (const student of testDetail.students) {
      try {
        await saveTestMarks(testDetail.testId, {
          reg_no: student.reg_no,
          marks: Object.fromEntries(testDetail.subjects.map((subject) => [subject, student.marks[subject] || ''])),
        });
        successCount += 1;
        savedRegNos.push(student.reg_no);
      } catch {
        failCount += 1;
      }
    }
    setSavingMarks(false);
    for (const regNo of savedRegNos) {
      const student = testDetail.students.find((item) => item.reg_no === regNo);
      if (!student) continue;
      testDetailOriginalMarksRef.current[regNo] = Object.fromEntries(
        testDetail.subjects.map((subject) => [subject, String(student.marks[subject] || '').trim()]),
      );
    }
    invalidateOverviewCaches(['dashboard', 'activity', 'activity-scope']);
    if (failCount === 0) {
      setFlash({ type: 'success', message: `Saved marks for ${successCount} students.` });
    } else {
      setFlash({ type: 'warning', message: `Save finished. Success: ${successCount}, Failed: ${failCount}.` });
    }
  }

  async function handleToggleTestBlock(test: ReportTestRecord) {
    try {
      await toggleTestBlock(test.id);
      setReportsData((prev) => (
        prev
          ? {
              ...prev,
              tests: prev.tests.map((entry) => (entry.id === test.id ? { ...entry, is_blocked: entry.is_blocked ? 0 : 1 } : entry)),
            }
          : prev
      ));
      invalidateOverviewCaches(['reports', 'dashboard', 'activity', 'activity-scope']);
      setFlash({ type: 'success', message: test.is_blocked ? 'Test unblocked.' : 'Test blocked.' });
      if (reportsData?.selectedDepartment && reportsData.selectedYear) {
        await loadReports(reportsData.selectedDepartment, reportsData.selectedYear, { preferCache: false });
      }
      if (testDetail?.testId === test.id) {
        await loadTestDetail(test.id);
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to update test status.' });
    }
  }

  async function handleDeleteTest(test: ReportTestRecord) {
    const confirmed = await requestConfirm({
      title: 'Delete Test',
      message: `Delete ${test.test_name} and all associated marks? This cannot be undone.`,
      confirmLabel: 'Delete',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fas fa-trash',
    });
    if (!confirmed) return;
    try {
      await deleteReportTest(test.id);
      setReportsData((prev) => (
        prev
          ? {
              ...prev,
              tests: prev.tests.filter((entry) => entry.id !== test.id),
            }
          : prev
      ));
      invalidateOverviewCaches(['reports', 'dashboard', 'activity', 'activity-scope']);
      setFlash({ type: 'success', message: 'Test deleted successfully.' });
      if (testDetail?.testId === test.id) {
        setTestDetail(null);
      }
      if (reportsData?.selectedDepartment && reportsData.selectedYear) {
        await loadReports(reportsData.selectedDepartment, reportsData.selectedYear, { preferCache: false });
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete test.' });
    }
  }

  async function handleUploadReport(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!reportsData?.selectedDepartment || !reportsData.selectedYear) return;
    if (!reportUploadDraft.test_name) {
      setFlash({ type: 'error', message: 'Select a test name before uploading the marksheet.' });
      return;
    }
    if (!reportUploadDraft.semester) {
      setFlash({ type: 'error', message: 'Select a semester before uploading the marksheet.' });
      return;
    }
    if (!reportUploadDraft.file) {
      setFlash({ type: 'error', message: 'Please choose a marks file to upload.' });
      return;
    }

    setUploadingReport(true);
    try {
      const batchName = reportUploadDraft.batch_name || getDefaultBatchNameForYearLevel(reportsData.selectedYear, bootstrap?.appConfig || null);
      const formData = new FormData(event.currentTarget);
      formData.set('marks_file', reportUploadDraft.file);
      formData.set('department', String(reportsData.selectedDepartment || '').trim().toUpperCase());
      formData.set('year_level', String(reportsData.selectedYear));
      formData.set('semester', String(reportUploadDraft.semester || '1'));
      formData.set('batch_name', batchName);
      formData.set('section', String(reportUploadDraft.section || '').trim());
      formData.set('test_name', String(reportUploadDraft.test_name || '').trim());
      formData.set('upload_mode', reportUploadDraft.upload_mode === 'replace' ? 'replace' : 'new');

      const result = await uploadMarksheet(formData);
      setFlash({
        type: result.parserWarnings.length ? 'warning' : 'success',
        message: result.parserWarnings.length
          ? `${result.message} Parser warnings: ${result.parserWarnings.join(' | ')}`
          : result.message,
      });
      invalidateOverviewCaches(['reports', 'dashboard', 'activity', 'activity-scope']);
      await loadReports(reportsData.selectedDepartment, reportsData.selectedYear, { preferCache: false });
      await loadTestDetail(result.testId);
      setReportUploadDraft({
        test_name: '',
        semester: '1',
        batch_name: '',
        section: '',
        upload_mode: 'new',
        file: null,
      });
      setReportUploadInputKey((value) => value + 1);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to upload marksheet.' });
    } finally {
      setUploadingReport(false);
    }
  }

  async function handleApplyNoticeFilters(event?: FormEvent<HTMLFormElement>) {
    event?.preventDefault();
    await loadNotices({
      department: noticeFilters.department || undefined,
      year: noticeFilters.year ? Number(noticeFilters.year) : null,
      status: noticeFilters.status || undefined,
      date_from: noticeFilters.date_from || undefined,
      date_to: noticeFilters.date_to || undefined,
    });
  }

  async function handleEditNotice(noticeId: number) {
    await loadNotices({
      department: noticeFilters.department || undefined,
      year: noticeFilters.year ? Number(noticeFilters.year) : null,
      status: noticeFilters.status || undefined,
      date_from: noticeFilters.date_from || undefined,
      date_to: noticeFilters.date_to || undefined,
      edit_id: noticeId,
    });
    window.requestAnimationFrame(() => {
      noticeComposerRef.current?.scrollIntoView({ behavior: 'smooth', block: 'start' });
    });
  }

  async function handleSaveNotice(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setSavingNotice(true);
    try {
      const buildNoticeFormData = (options?: { noticeId?: number | null; deferAttachments?: boolean; includeRemovals?: boolean }) => {
        const formData = new FormData();
        const resolvedNoticeId = Number(options?.noticeId || noticeForm.notice_id || 0) || 0;
        if (resolvedNoticeId) formData.set('notice_id', String(resolvedNoticeId));
        formData.set('notice_title', noticeForm.notice_title);
        formData.set('notice_message_text', noticeForm.notice_message_text);
        if (noticeForm.notice_send_to_all) formData.set('notice_send_to_all', 'on');
        if (options?.deferAttachments) formData.set('defer_attachments', '1');
        for (const scopeValue of noticeForm.scope_pairs) formData.append('notice_scope_pairs', scopeValue);
        if (options?.includeRemovals !== false) {
          for (const attachmentId of noticeForm.remove_attachment_ids) formData.append('remove_attachment_ids', String(attachmentId));
        }
        return formData;
      };

      let targetNoticeId = Number(noticeForm.notice_id || 0) || 0;
      const pendingFiles = [...noticeForm.files];

      if (!targetNoticeId) {
        const result = await saveNotice(buildNoticeFormData({ deferAttachments: pendingFiles.length > 0 }));
        targetNoticeId = Number(result.noticeId || 0) || 0;
      } else {
        await saveNotice(buildNoticeFormData({ noticeId: targetNoticeId }));
      }

      for (const file of pendingFiles) {
        await uploadNoticeAttachmentInChunks(targetNoticeId, file);
      }

      setFlash({ type: 'success', message: noticeForm.notice_id ? 'Notice updated successfully.' : 'Notice created successfully.' });
      await loadNotices({
        department: noticeFilters.department || undefined,
        year: noticeFilters.year ? Number(noticeFilters.year) : null,
        status: noticeFilters.status || undefined,
        date_from: noticeFilters.date_from || undefined,
        date_to: noticeFilters.date_to || undefined,
      });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to save notice.' });
    } finally {
      setSavingNotice(false);
    }
  }

  function handleNoticeFilesSelected(nextFiles: FileList | null) {
    const incoming = Array.from(nextFiles || []);
    if (!incoming.length) return;

    setNoticeForm((prev) => {
      const existingKeys = new Set(prev.files.map((file) => `${file.name}:${file.size}:${file.lastModified}`));
      const merged = [...prev.files];
      for (const file of incoming) {
        const key = `${file.name}:${file.size}:${file.lastModified}`;
        if (existingKeys.has(key)) continue;
        merged.push(file);
        existingKeys.add(key);
      }
      return { ...prev, files: merged };
    });
    setNoticeFileInputKey((prev) => prev + 1);
  }

  function handleRemovePendingNoticeFile(targetIndex: number) {
    setNoticeForm((prev) => ({
      ...prev,
      files: prev.files.filter((_, index) => index !== targetIndex),
    }));
  }

  async function handleDeleteNoticeAction(notice: NoticeRecord) {
    const shouldDelete = await requestConfirm({
      title: 'Delete Notice',
      message: `Delete "${notice.title_display}" and its attachment records?`,
      confirmLabel: 'Delete',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fas fa-trash',
    });
    if (!shouldDelete) return;
    try {
      await deleteNoticeRecord(notice.id);
      setFlash({ type: 'success', message: 'Notice deleted successfully.' });
      if (noticeForm.notice_id === notice.id) applyNoticeEditState(null);
      await loadNotices({
        department: noticeFilters.department || undefined,
        year: noticeFilters.year ? Number(noticeFilters.year) : null,
        status: noticeFilters.status || undefined,
        date_from: noticeFilters.date_from || undefined,
        date_to: noticeFilters.date_to || undefined,
      });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete notice.' });
    }
  }

  function resetUserCreateForm(nextRole?: Role) {
    const resolvedRole = nextRole || userAssignableRoles[0] || (currentUser?.role === 'deo' ? 'counselor' : 'counselor');
    const nextState = {
      name: '',
      email: '',
      password: '',
      confirm_password: '',
      role: resolvedRole,
      designation: resolvedRole === 'principal' ? 'Higher Official' : '',
      department: '',
      year_level: '1',
      max_students: '30',
      scope_pairs: [],
    };
    setUserCreateForm(nextState);
    try {
      window.localStorage.removeItem(USER_CREATE_DRAFT_STORAGE_KEY);
    } catch {
      // Ignore localStorage cleanup failures.
    }
  }

  function handleClearUserCreateDraft() {
    resetUserCreateForm();
  }

  async function handleCreateUser(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!userCreateEmailDomainValid) {
      setFlash({ type: 'error', message: `Only ${managedUserDomain} email accounts are allowed.` });
      return;
    }
    if (userCreateEmailExists && !userCreateAvailableRoles.length) {
      setFlash({ type: 'error', message: 'This email already has all assignable roles.' });
      return;
    }
    setUserSaving(true);
    try {
      await createUserAccount({
        ...userCreateForm,
        max_students: Number(userCreateForm.max_students || 30),
        year_level: Number(userCreateForm.year_level || 1),
      });
      setFlash({ type: 'success', message: 'User created successfully.' });
      resetUserCreateForm();
      await refreshUsersOverview({ preferCache: false });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to create user.' });
    } finally {
      setUserSaving(false);
    }
  }

  function openEditUserModal(user: UserRecord) {
    setUserEditDraft({
      original_email: user.account_email || user.email,
      name: user.name,
      email: user.email,
      password: '',
      role: user.role,
      designation: user.role === 'principal' ? String(user.designation || '').trim() || 'Higher Official' : '',
      department: user.department || '',
      year_level: String(user.year_level || 1),
      max_students: String(user.max_students || 30),
      scope_pairs: (user.scopes || []).map((scope) => `${scope.department}::${scope.year_level}`),
    });
  }

  async function handleSaveUserEdit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!userEditDraft) return;
    const originalEmail = String(userEditDraft.original_email || '').trim().toLowerCase();
    const nextEmail = String(userEditDraft.email || '').trim().toLowerCase();
    setUserSaving(true);
    try {
      await updateUserAccount(userEditDraft.original_email, {
        ...userEditDraft,
        max_students: Number(userEditDraft.max_students || 30),
        year_level: Number(userEditDraft.year_level || 1),
      });
      setUserEditDraft(null);
      setFlash({ type: 'success', message: 'User updated successfully.' });
      await refreshUsersOverview({ preferCache: false });
      if (originalEmail === String(currentUser?.email || '').trim().toLowerCase() || nextEmail !== originalEmail) {
        await refreshBootstrap({ targetTab: activeTab });
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to update user.' });
    } finally {
      setUserSaving(false);
    }
  }

  async function handleConfirmUserAction() {
    if (!userActionTarget) return;
    setUserActionLoading(true);
    try {
      if (userActionTarget.kind === 'lock') {
        await lockUserAccount(userActionTarget.user.account_email || userActionTarget.user.email);
      } else if (userActionTarget.kind === 'unlock') {
        await unlockUserAccount(userActionTarget.user.account_email || userActionTarget.user.email);
      } else {
        await deleteUserAccount(userActionTarget.user.account_email || userActionTarget.user.email);
      }
      setFlash({
        type: 'success',
        message:
          userActionTarget.kind === 'delete'
            ? 'User deleted successfully.'
            : userActionTarget.kind === 'lock'
              ? 'User locked successfully.'
              : 'User unlocked successfully.',
      });
      setUserActionTarget(null);
      await refreshUsersOverview({ preferCache: false });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to update user.' });
    } finally {
      setUserActionLoading(false);
    }
  }

  async function handleBulkCounselorUpload(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!bulkCounselorForm.file) {
      setFlash({ type: 'warning', message: 'Select an Excel file to continue.' });
      return;
    }
    setBulkCounselorSaving(true);
    try {
      const formData = new FormData();
      formData.set('year_level', bulkCounselorForm.year_level || '1');
      formData.set('file', bulkCounselorForm.file);
      const result = await uploadBulkCounselors(formData);
      setFlash({ type: 'success', message: result.message || 'Bulk counselor upload completed.' });
      setBulkCounselorForm({ year_level: '1', file: null });
      setBulkCounselorUploadKey((value) => value + 1);
      await refreshUsersOverview({ preferCache: false });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to upload counselors.' });
    } finally {
      setBulkCounselorSaving(false);
    }
  }

  async function handleCreateDepartment(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    try {
      await createDepartment(departmentForm.code, departmentForm.name);
      setDepartmentForm({ code: '', name: '' });
      setFlash({ type: 'success', message: 'Department added successfully.' });
      await refreshDepartments();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to add department.' });
    }
  }

  async function handleUpdateDepartment(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!departmentEdit) return;
    try {
      await updateDepartment(departmentEdit.id, departmentEdit.code, departmentEdit.name);
      setDepartmentEdit(null);
      setFlash({ type: 'success', message: 'Department updated successfully.' });
      await refreshDepartments();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to update department.' });
    }
  }

  function handleToggleDepartment(department: DepartmentRecord) {
    setDepartmentActionState({ kind: 'toggle', department });
  }

  async function handleConfirmDepartmentAction() {
    if (!departmentActionState) return;
    setDepartmentActionLoading(true);
    try {
      if (departmentActionState.kind === 'toggle') {
        await toggleDepartment(departmentActionState.department.id);
        setFlash({
          type: 'success',
          message: `${departmentActionState.department.code} ${departmentActionState.department.is_active ? 'disabled' : 'enabled'} successfully.`,
        });
      } else {
        await deleteDepartment(departmentActionState.department.id);
        setFlash({ type: 'success', message: `Department ${departmentActionState.department.code} deleted.` });
        if (departmentEdit?.id === departmentActionState.department.id) {
          setDepartmentEdit(null);
        }
      }
      setDepartmentActionState(null);
      await refreshDepartments();
    } catch (error) {
      setFlash({
        type: 'error',
        message: error instanceof Error
          ? error.message
          : departmentActionState.kind === 'toggle'
            ? 'Failed to update department status.'
            : 'Failed to delete department.',
      });
    } finally {
      setDepartmentActionLoading(false);
    }
  }

  function handleDeleteDepartment(department: DepartmentRecord) {
    setDepartmentActionState({ kind: 'delete', department });
  }

  async function handleApplyActivityFilters(event?: FormEvent<HTMLFormElement>) {
    event?.preventDefault();
    await loadActivityOverview({
      department: activityFilters.department || undefined,
      year: activityFilters.year ? Number(activityFilters.year) : null,
      semester: activityFilters.semester || undefined,
      test_name: activityFilters.test_name || undefined,
      q: activityFilters.q || undefined,
      sort: activityFilters.sort || undefined,
    });
  }

  async function handleCopyPreparedLines(
    lines: CopyLine[],
    title: string,
    successMessage: string,
    preferImage = false,
  ) {
    try {
      if (preferImage) {
        const svg = buildCopyCardSvg(title, lines);
        await copySvgImageToClipboard(svg);
      } else {
        await navigator.clipboard.writeText(renderCopyLinesAsText(lines));
      }
      setConfirmDialog({
        title: preferImage ? 'Image Copied' : 'Copied',
        message: successMessage,
        confirmLabel: 'OK',
        confirmClassName: 'btn btn-primary btn-sm',
        iconClassName: preferImage ? 'fas fa-image' : 'fas fa-copy',
        cancelLabel: null,
      });
    } catch {
      if (preferImage) {
        try {
          await navigator.clipboard.writeText(renderCopyLinesAsText(lines));
          setConfirmDialog({
            title: 'Copied As Text',
            message: `${successMessage} Image copy was not available on this device, so a text version was copied instead.`,
            confirmLabel: 'OK',
            confirmClassName: 'btn btn-primary btn-sm',
            iconClassName: 'fas fa-copy',
            cancelLabel: null,
          });
          return;
        } catch {
          // Fall through to error flash below.
        }
      }
      setFlash({ type: 'error', message: 'Failed to copy defaulters list.' });
    }
  }

  async function handleCopyActivityDefaulters(
    mode: 'scope' | 'department' | 'year' | 'test',
    filters?: {
      department?: string;
      year?: number | null;
      semester?: string;
      test_name?: string;
    },
  ) {
    setActivityCopying(true);
    try {
      const payload = await getCachedActivityScopeReport(filters);
      const pendingCount = (payload.sections || []).reduce(
        (sum, section) => sum + section.rows.filter((row) => Number(row.pending_count || 0) > 0).length,
        0,
      );
      if (!pendingCount) {
        setFlash({ type: 'warning', message: 'No defaulters were found for the selected counselor activity scope.' });
        return;
      }
      const renderedText = renderCopyTemplate(
        String(bootstrap?.appConfig?.activity_defaulter_copy_template || DEFAULT_ACTIVITY_DEFAULTER_COPY_TEMPLATE),
        {
          count: String(pendingCount),
          mode,
          entries: buildActivityCopyEntries(payload.sections || []),
        },
      );
      await handleCopyPreparedLines(
        plainTextToCopyLines(renderedText),
        'Counselor Activity Defaulters',
        `Copied ${pendingCount} pending counselor entr${pendingCount === 1 ? 'y' : 'ies'} from counselor activity.`,
        String(bootstrap?.appConfig?.activity_copy_as_image || 'false').toLowerCase() === 'true',
      );
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to prepare activity defaulters list.' });
    } finally {
      setActivityCopying(false);
    }
  }

  async function handleDownloadActivityScopePdf(filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
  }) {
    setActivityPdfLoading(true);
    try {
      const result = await downloadActivityScopeReportPdf(filters);
      const objectUrl = URL.createObjectURL(result.blob);
      const link = document.createElement('a');
      link.href = objectUrl;
      link.download = result.filename || 'activity_scope_report.pdf';
      document.body.appendChild(link);
      link.click();
      link.remove();
      window.setTimeout(() => URL.revokeObjectURL(objectUrl), 1000);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to export counselor activity PDF.' });
    } finally {
      setActivityPdfLoading(false);
    }
  }

  async function handleDeleteAdminMessage(id: number) {
    const confirmed = await requestConfirm({
      title: 'Delete Message',
      message: 'Delete this message entry?',
      confirmLabel: 'Delete',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fas fa-trash',
    });
    if (!confirmed) return;
    try {
      await deleteAdminMessage(id);
      setFlash({ type: 'success', message: 'Message log deleted.' });
      await loadAdminMessages(adminMessageFilters);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete message entry.' });
    }
  }

  async function handleDeleteSelectedAdminMessages() {
    if (!selectedAdminMessageIds.length) {
      setFlash({ type: 'warning', message: 'Select at least one message row first.' });
      return;
    }
    const confirmed = await requestConfirm({
      title: 'Delete Selected Messages',
      message: `Delete ${selectedAdminMessageIds.length} selected message records?`,
      confirmLabel: 'Delete Selected',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fas fa-trash',
    });
    if (!confirmed) return;
    try {
      await deleteAdminMessages(selectedAdminMessageIds);
      setFlash({ type: 'success', message: 'Selected message logs deleted.' });
      await loadAdminMessages(adminMessageFilters);
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete selected messages.' });
    }
  }

  async function handleCopyNoticeDefaulters() {
    const pendingRows = noticeCompletionRows.filter((row) => (row.pending_notice_count || 0) > 0);
    if (!pendingRows.length) {
      setFlash({ type: 'warning', message: 'No pending counselors found for the current completion filters.' });
      return;
    }
    const renderedText = renderCopyTemplate(
      String(bootstrap?.appConfig?.notice_defaulter_copy_template || DEFAULT_NOTICE_DEFAULTER_COPY_TEMPLATE),
      {
        count: String(pendingRows.length),
        entries: buildNoticeCopyEntries(pendingRows),
      },
    );
    await handleCopyPreparedLines(
      plainTextToCopyLines(renderedText),
      'Notice Defaulters',
      `Copied ${pendingRows.length} pending counselor entr${pendingRows.length === 1 ? 'y' : 'ies'} from notices.`,
      String(bootstrap?.appConfig?.notice_copy_as_image || 'false').toLowerCase() === 'true',
    );
  }

  async function handleCopyDashboardNoticeDefaulters() {
    try {
      const payload = await getNoticesOverview();
      const pendingRows = (payload.completionRows || []).filter((row) => (row.pending_notice_count || 0) > 0);
      if (!pendingRows.length) {
        setFlash({ type: 'warning', message: 'No pending counselors found for the current notice scope.' });
        return;
      }
      const renderedText = renderCopyTemplate(
        String(bootstrap?.appConfig?.notice_defaulter_copy_template || DEFAULT_NOTICE_DEFAULTER_COPY_TEMPLATE),
        {
          count: String(pendingRows.length),
          entries: buildNoticeCopyEntries(pendingRows),
        },
      );
      await handleCopyPreparedLines(
        plainTextToCopyLines(renderedText),
        'Notice Defaulters',
        `Copied ${pendingRows.length} pending counselor entr${pendingRows.length === 1 ? 'y' : 'ies'} from notices.`,
        String(bootstrap?.appConfig?.notice_copy_as_image || 'false').toLowerCase() === 'true',
      );
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to prepare notice defaulters list.' });
    }
  }

  async function handleLogoutAllUsers() {
    const confirmed = await requestConfirm({
      title: 'Logout All Users',
      message: 'Logout all active users now?',
      confirmLabel: 'Logout All',
      confirmClassName: 'btn btn-warning btn-sm',
      iconClassName: 'fas fa-power-off',
    });
    if (!confirmed) return;
    try {
      await logoutAllSessions();
      setFlash({ type: 'success', message: 'All active sessions were logged out.' });
      await loadMonitoringOverview();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to logout all users.' });
    }
  }

  async function handleForceLogout(email: string) {
    const confirmed = await requestConfirm({
      title: 'Force Logout',
      message: `Force logout ${email}?`,
      confirmLabel: 'Force Logout',
      confirmClassName: 'btn btn-warning btn-sm',
      iconClassName: 'fas fa-power-off',
    });
    if (!confirmed) return;
    try {
      await forceLogoutSession(email);
      await loadMonitoringOverview();
      setFlash({ type: 'success', message: `${email} was logged out.` });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to force logout user.' });
    }
  }

  async function handleCleanupSessions() {
    try {
      await cleanupSessions();
      setFlash({ type: 'success', message: 'Inactive sessions were cleaned up.' });
      await loadMonitoringOverview();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to clean inactive sessions.' });
    }
  }

  async function handleCreateBackup(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setDatabaseBackupCreating(true);
    try {
      setDatabaseProgress({
        title: 'Creating Backup',
        body: `Creating backup ${String(databaseBatchName || '').trim() || 'for the current batch'}. Please wait while the rebuild saves the database snapshot.`,
      });
      const result = await createDatabaseBackup(databaseBatchName, databaseOverwrite);
      setFlash({ type: 'success', message: result.message });
      setDatabaseOverwrite(false);
      await loadDatabaseOverview();
      setDatabaseProgress(null);
    } catch (error) {
      setDatabaseProgress(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to create backup.' });
    } finally {
      setDatabaseBackupCreating(false);
    }
  }

  async function handleConfirmDatabaseBackupAction(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!databaseBackupAction) return;
    setDatabaseActionLoading(true);
    try {
      if (databaseBackupAction.kind === 'archive') {
        setDatabaseProgress({
          title: 'Archiving Academic Year',
          body: `Creating archive_${archiveYearLabel.replace(/[^0-9A-Za-z_-]/g, '_')}.db and resetting the active workspace. Please wait...`,
        });
        const result = await archiveAcademicYear(archiveYearLabel, databaseActionPassword, archiveYearOverwrite);
        if (result.reload) {
          window.setTimeout(() => reloadCurrentApp(), 350);
          return;
        }
        setFlash({ type: 'success', message: 'Academic year archived successfully.' });
        setDatabaseBackupAction(null);
        setDatabaseActionPassword('');
        setArchiveYearStart('');
        setArchiveYearEnd('');
        setArchiveYearOverwrite(false);
        await loadDatabaseOverview();
        return;
      }

      if (databaseBackupAction.kind === 'delete-archive') {
        await deleteArchiveYear(databaseBackupAction.backupName, databaseActionPassword);
        setFlash({ type: 'success', message: `Deleted archive ${databaseBackupAction.backupName}.` });
        setDatabaseBackupAction(null);
        setDatabaseActionPassword('');
        await loadDatabaseOverview();
        return;
      }

      if (databaseBackupAction.kind === 'clear') {
        const result = await clearExamDatabase(databaseActionPassword);
        if (result.relogin) {
          window.setTimeout(() => reloadCurrentApp(), 350);
          return;
        }
        invalidateOverviewCaches(['dashboard', 'reports', 'cdp', 'activity', 'activity-scope', 'users']);
        subjectsOverviewCacheRef.current.clear();
        setTestDetail(null);
        setFlash({ type: 'success', message: 'Active database cleared successfully.' });
        setDatabaseBackupAction(null);
        setDatabaseActionPassword('');
        await loadDatabaseOverview();
        return;
      }

      if (databaseBackupAction.kind === 'delete') {
        await deleteDatabaseBackup(databaseBackupAction.backupName, databaseActionPassword);
        setFlash({ type: 'success', message: `Deleted backup ${databaseBackupAction.backupName}.` });
        setDatabaseBackupAction(null);
        setDatabaseActionPassword('');
        await loadDatabaseOverview();
        return;
      }

      if (databaseBackupAction.kind === 'restore-archive') {
        setDatabaseProgress({
          title: 'Restoring Archive',
          body: `Restoring ${databaseBackupAction.backupName}. Please wait while the rebuild reconnects to the archived academic year.`,
        });
        const result = await restoreArchiveYear(databaseBackupAction.backupName, databaseActionPassword);
        if (result.relogin || result.reload) {
          window.setTimeout(() => reloadCurrentApp(), 350);
          return;
        }
        setFlash({ type: 'success', message: `Restored archive ${databaseBackupAction.backupName}.` });
        setDatabaseBackupAction(null);
        setDatabaseActionPassword('');
        await loadDatabaseOverview();
        return;
      }

      setDatabaseProgress({
        title: 'Restoring Backup',
        body: `Restoring ${databaseBackupAction.backupName}. Please wait while the rebuild reconnects to the restored data.`,
      });
      const result = await restoreDatabaseBackup(databaseBackupAction.backupName, databaseActionPassword);
      if (result.relogin || result.reload) {
        window.setTimeout(() => reloadCurrentApp(), 350);
        return;
      }
      setFlash({ type: 'success', message: `Restored backup ${databaseBackupAction.backupName}.` });
      setDatabaseBackupAction(null);
      setDatabaseActionPassword('');
      await loadDatabaseOverview();
    } catch (error) {
      setDatabaseProgress(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Database action failed.' });
    } finally {
      setDatabaseActionLoading(false);
    }
  }

  async function handleArchiveYear(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!String(archiveYearLabel || '').trim()) {
      setFlash({ type: 'error', message: 'Enter the academic year range to archive.' });
      return;
    }
    setDatabaseActionPassword('');
    setDatabaseBackupAction({
      kind: 'archive',
      backupName: `archive_${archiveYearLabel.replace(/[^0-9A-Za-z_-]/g, '_')}.db`,
    });
  }

  async function handleEnterArchiveView(archiveName: string) {
    try {
      setDatabaseProgress({
        title: 'Opening Archive View',
        body: `Loading ${archiveName} in read-only mode. The workspace will refresh into archive view.`,
      });
      const result = await enterArchiveView(archiveName);
      if (result.reload) {
        window.setTimeout(() => reloadCurrentApp(), 250);
        return;
      }
      setDatabaseProgress(null);
      await refreshBootstrap({ targetTab: activeTab });
      await loadDatabaseOverview();
    } catch (error) {
      setDatabaseProgress(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to open archive view.' });
    }
  }

  async function handleExitArchiveView() {
    try {
      setDatabaseProgress({
        title: 'Leaving Archive View',
        body: 'Restoring the live workspace and refreshing your current session.',
      });
      const result = await exitArchiveView();
      if (result.reload) {
        window.setTimeout(() => reloadCurrentApp(), 250);
        return;
      }
      setDatabaseProgress(null);
      await refreshBootstrap({ targetTab: activeTab });
      await loadDatabaseOverview();
    } catch (error) {
      setDatabaseProgress(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to exit archive view.' });
    }
  }

  async function persistConfig(adminPassword = '') {
    setConfigSaving(true);
    try {
      const result = await updateConfig({
        ...configForm,
        admin_password: otpPolicyChanged ? adminPassword : '',
      });
      const nextConfigData: ConfigOverviewPayload = {
        appConfig: result.appConfig,
        envContent: envDraft,
        smtpStatus: result.smtpStatus,
        resetUsers: configData?.resetUsers || [],
      };
      setConfigData(nextConfigData);
      applyConfigPayload(nextConfigData);
      setBootstrap((prev) => (prev ? { ...prev, appConfig: result.appConfig } : prev));
      applyThemeColors(result.appConfig);
      if (result.relogin) {
        clearRememberedAuthState();
        setFlash({ type: 'success', message: 'OTP login policy changed. All users were logged out and you have been returned to sign in.' });
        await refreshBootstrap();
        return { relogin: true };
      }
      setFlash({ type: 'success', message: 'Settings saved successfully.' });
      return { relogin: false };
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to save settings.' });
      return null;
    } finally {
      setConfigSaving(false);
    }
  }

  async function handleSaveConfig(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (otpPolicyChanged) {
      setConfigPromptPassword('');
      setConfigPasswordPrompt({ nextTab: null });
      return;
    }
    await persistConfig('');
  }

  async function handleConfirmConfigPassword() {
    if (otpPolicyChanged && !String(configPromptPassword || '').trim()) {
      setFlash({ type: 'error', message: 'Enter your admin password to change the OTP login policy.' });
      return;
    }
    const nextTab = configPasswordPrompt?.nextTab || null;
    const result = await persistConfig(configPromptPassword);
    if (!result) return;
    setConfigPasswordPrompt(null);
    setConfigPromptPassword('');
    setPendingConfigTab(null);
    if (!result.relogin && nextTab) {
      setActiveTab(nextTab);
      setMobileSidebarOpen(false);
    }
  }

  function discardConfigChanges(nextTab?: string | null) {
    if (configData) {
      applyConfigPayload(configData);
    }
    setPendingConfigTab(null);
    if (nextTab) {
      setActiveTab(nextTab);
      setMobileSidebarOpen(false);
    }
  }

  function handleSidebarTabNavigation(tab: string) {
    if (activeTab === 'config' && configFormDirty && tab !== 'config') {
      setPendingConfigTab(tab);
      return;
    }
    setActiveTab(tab);
    setMobileSidebarOpen(false);
    if (tab === 'reports') {
      void loadReports();
    }
    if (tab === 'test-database') {
      setTestDetail(null);
      setCounselorSendPage(null);
      setCounselorSendVerify(null);
    }
  }

  async function handleSaveEnvContent(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setEnvSaving(true);
    try {
      await updateEnvContent(envDraft);
      setFlash({ type: 'success', message: '.env content saved successfully.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to save .env content.' });
    } finally {
      setEnvSaving(false);
    }
  }

  async function handleRefreshSmtpStatus() {
    try {
      const payload = await getSmtpStatus();
      setConfigData((prev) => (prev ? { ...prev, smtpStatus: payload.status } : prev));
      setFlash({ type: 'info', message: payload.status.detail || payload.status.label });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to refresh SMTP status.' });
    }
  }

  async function handleDownloadConfigExport() {
    try {
      const { blob, fileName } = await downloadConfigExport();
      const objectUrl = window.URL.createObjectURL(blob);
      const anchor = document.createElement('a');
      anchor.href = objectUrl;
      anchor.download = fileName;
      document.body.appendChild(anchor);
      anchor.click();
      anchor.remove();
      window.URL.revokeObjectURL(objectUrl);
      setFlash({ type: 'success', message: 'Settings export downloaded successfully.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to download settings export.' });
    }
  }

  async function handleImportConfigFile(event: ChangeEvent<HTMLInputElement>) {
    const file = event.target.files?.[0];
    if (!file) return;
    setConfigImporting(true);
    try {
      const content = await file.text();
      const parsed = JSON.parse(content) as Record<string, unknown>;
      const payload = await importConfigPayload(parsed);
      applyConfigPayload(payload);
      setBootstrap((prev) => (prev ? { ...prev, appConfig: payload.appConfig } : prev));
      applyThemeColors(payload.appConfig);
      setFlash({ type: 'success', message: 'Settings imported successfully.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to import settings file.' });
    } finally {
      if (event.target) event.target.value = '';
      setConfigImporting(false);
    }
  }

  async function handleRunSmtpTest() {
    setSmtpTesting(true);
    try {
      const result = await runSmtpTest();
      setFlash({ type: result.success ? 'success' : 'warning', message: result.message });
      await handleRefreshSmtpStatus();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'SMTP test failed.' });
    } finally {
      setSmtpTesting(false);
    }
  }

  async function handleResetUserPassword(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setResetSaving(true);
    try {
      await resetUserPassword(resetPasswordDraft);
      setResetPasswordDraft({
        target_email: '',
        new_password: '',
        confirm_password: '',
        force_logout: true,
      });
      setResetUserSearch('');
      setFlash({ type: 'success', message: 'User password reset successfully.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to reset user password.' });
    } finally {
      setResetSaving(false);
    }
  }

  if (bootLoading) {
    return (
      <main className="login-layout">
        <div className="login-box">
          <div className="login-logo">
            <div className="login-banner-wrap">
              <img src="/assets/banner.png" alt="RMKCET Banner" className="login-banner-image" />
            </div>
            <p>RMKCET SHINE : RMKCET Science and Humanities Internal Notification Engine</p>
          </div>
          <div className="boot-loader-block" aria-live="polite">
            <div className="spinner-ring boot-loader-ring" aria-hidden="true"></div>
            <div className="boot-loader-text">Loading workspace</div>
            <div className="boot-loader-dots" aria-hidden="true">
              <span></span>
              <span></span>
              <span></span>
            </div>
          </div>
        </div>
      </main>
    );
  }

  if (!currentUser) {
    return (
      <>
      <main className="login-layout">
        <div className="login-box">
          <div className="login-logo">
            <div className="login-banner-wrap">
              <img src="/assets/banner.png" alt="RMKCET Banner" className="login-banner-image" />
            </div>
            <p>RMKCET SHINE : RMKCET Science and Humanities Internal Notification Engine</p>
          </div>

          {loginState.conflict ? (
            <div className="session-conflict-alert">
              <div className="conflict-icon"><i className="fas fa-exclamation-triangle"></i></div>
              <h3>Active Session Detected</h3>
              <p>You are already logged in on another device.</p>
              <div className="device-info">
                <p><i className="fas fa-desktop"></i> <strong>Device:</strong> {loginState.conflict.device_type}</p>
                <p><i className="fas fa-globe"></i> <strong>Browser:</strong> {loginState.conflict.browser}</p>
                <p><i className="fas fa-map-marker-alt"></i> <strong>IP:</strong> {loginState.conflict.ip_address || 'Unknown'}</p>
                <p><i className="fas fa-clock"></i> <strong>Logged in:</strong> {loginState.conflict.login_time?.slice(0, 16) || 'Unknown'}</p>
              </div>
              {loginState.conflictAuthMethod === 'google' && loginConflictHasUnknownDetails(loginState.conflict) ? (
                <div className="flash flash-info" style={{ marginBottom: 14 }}>
                  <i className="fas fa-circle-info"></i>
                  <span>We found the active Google session, but its device details were not available. Continuing will still log it out.</span>
                </div>
              ) : null}
              <p className="conflict-question">Do you want to logout from the other device and continue here?</p>
              <div className="conflict-buttons">
                <button
                  type="button"
                  className="btn btn-primary"
                  onClick={() => {
                    if (loginRoleSelectionState?.selectedAccountEmail) {
                      void handleCompleteLoginRoleSelection(true);
                      return;
                    }
                    if (loginState.conflictAuthMethod === 'google') {
                      void handleResolveGoogleLoginConflict();
                      return;
                    }
                    const fakeEvent = { preventDefault() {} } as FormEvent<HTMLFormElement>;
                    void handleLogin(fakeEvent, true);
                  }}
                  disabled={loginState.loading}
                >
                  <i className={`fas ${loginState.loading ? 'fa-spinner fa-spin' : 'fa-sign-out-alt'}`}></i>{' '}
                  {loginState.loading ? 'Continuing...' : 'Yes, Logout Other Device'}
                </button>
                <button
                  type="button"
                  className="btn btn-outline"
                  onClick={() => {
                    setLoginConflictInfoOpen(false);
                    setLoginState((prev) => ({ ...prev, conflict: null, conflictAuthMethod: null, error: '' }));
                  }}
                  disabled={loginState.loading}
                >
                  <i className="fas fa-times"></i> Cancel
                </button>
              </div>
            </div>
          ) : loginRoleSelectionState ? (
            <>
              <form
                onSubmit={(event) => {
                  event.preventDefault();
                  void handleCompleteLoginRoleSelection(false);
                }}
              >
                <div className="form-group">
                  <label className="form-label">Select Role</label>
                  <div className="card" style={{ padding: 12, marginBottom: 12 }}>
                    <div style={{ fontSize: '.82rem', color: 'var(--text-dim)', marginBottom: 10 }}>
                      This email is linked to multiple SHINE roles. Choose the workspace you want to open for <strong>{loginRoleSelectionState.loginEmail}</strong>.
                    </div>
                    <div style={{ display: 'grid', gap: 8 }}>
                      {loginRoleSelectionState.options.map((option) => (
                        <label
                          key={option.accountEmail}
                          className="scope-chip"
                          style={{
                            display: 'flex',
                            alignItems: 'center',
                            gap: 10,
                            padding: '12px 14px',
                            borderRadius: 12,
                            border: option.accountEmail === loginRoleSelectionState.selectedAccountEmail ? '1px solid var(--primary)' : '1px solid var(--border)',
                            background: option.accountEmail === loginRoleSelectionState.selectedAccountEmail ? 'rgba(102,126,234,.12)' : 'var(--bg-input)',
                          }}
                        >
                          <input
                            type="radio"
                            name="login-role-selection"
                            checked={option.accountEmail === loginRoleSelectionState.selectedAccountEmail}
                            onChange={() => setLoginRoleSelectionState((prev) => prev ? { ...prev, selectedAccountEmail: option.accountEmail } : prev)}
                          />
                          <span style={{ display: 'grid', gap: 3 }}>
                            <strong>{getRoleOptionLabel(option.role, option.designation)}</strong>
                            <span className="inline-muted">
                              {option.name}
                              {option.department ? ` • ${option.department}` : ''}
                              {option.role === 'counselor' ? ` • ${formatYearLevel(option.year_level || 1)}` : ''}
                            </span>
                          </span>
                        </label>
                      ))}
                    </div>
                  </div>
                </div>

                {loginState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{loginState.error}</span>
                  </div>
                ) : null}

                <button type="submit" className="btn btn-primary" style={{ marginTop: 8 }} disabled={loginState.loading}>
                  <i className={`fas ${loginState.loading ? 'fa-spinner fa-spin' : 'fa-right-to-bracket'}`}></i> {loginState.loading ? 'Opening...' : 'Continue'}
                </button>
              </form>

              <div className="d-flex" style={{ gap: 10, marginTop: 10 }}>
                <button
                  type="button"
                  className="btn btn-outline"
                  style={{ flex: 1 }}
                  onClick={() => {
                    setLoginRoleSelectionState(null);
                    setLoginState((prev) => ({ ...prev, loading: false, error: '', conflict: null, conflictAuthMethod: null }));
                  }}
                  disabled={loginState.loading}
                >
                  <i className="fas fa-arrow-left"></i> Back
                </button>
              </div>
            </>
          ) : loginOtpState ? (
            <>
              <form onSubmit={(event) => void handleVerifyLoginOtp(event)} autoComplete="off">
                <div className="form-group">
                  <label className="form-label" htmlFor="loginOtpCode">Login OTP</label>
                  <input
                    type="text"
                    className="form-control otp-code-input"
                    id="loginOtpCode"
                    inputMode="numeric"
                    autoComplete="one-time-code"
                    pattern="\d{6}"
                    placeholder="Enter 6-digit OTP"
                    minLength={6}
                    maxLength={6}
                    value={loginState.otp_code}
                    onChange={(event) => setLoginState((prev) => ({ ...prev, otp_code: normalizeOtpCode(event.target.value) }))}
                    required
                    autoFocus
                  />
                  <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', marginTop: 4, display: 'block' }}>
                    OTP sent to {loginOtpState.maskedEmail || 'your email'}
                  </small>
                </div>

                {loginState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{loginState.error}</span>
                  </div>
                ) : null}

                <button type="submit" className="btn btn-primary" style={{ marginTop: 8 }} disabled={loginState.loading}>
                  <i className="fas fa-shield-check"></i> {loginState.loading ? 'Verifying...' : 'Verify OTP'}
                </button>
              </form>

              <div className="d-flex" style={{ gap: 10, marginTop: 10 }}>
                <button type="button" className="btn btn-outline" style={{ flex: 1 }} onClick={() => void handleResendLoginOtp()} disabled={loginState.loading}>
                  <i className="fas fa-paper-plane"></i> Resend OTP
                </button>
                <button type="button" className="btn btn-outline" style={{ flex: 1 }} onClick={() => void handleCancelLoginOtp()} disabled={loginState.loading}>
                  <i className="fas fa-arrow-left"></i> Back
                </button>
              </div>
            </>
          ) : (
            <form onSubmit={(event) => void handleLogin(event)}>
              {flash ? (
                <div className={`flash flash-${flash.type}`} style={{ marginBottom: 14 }}>
                  <i className={`fas ${flash.type === 'success' ? 'fa-check-circle' : flash.type === 'warning' ? 'fa-exclamation-triangle' : flash.type === 'error' ? 'fa-times-circle' : 'fa-info-circle'}`}></i>
                  <span>{flash.message}</span>
                  <button className="flash-close" type="button" onClick={() => setFlash(null)}><i className="fas fa-times"></i></button>
                </div>
              ) : null}

              <div className="form-group">
                <label className="form-label" htmlFor="identifier">Email or Name</label>
                <input
                  type="text"
                  className="form-control"
                  id="identifier"
                  placeholder="Enter your email or name"
                  value={loginState.identifier}
                  onChange={(event) => setLoginState((prev) => ({ ...prev, identifier: event.target.value }))}
                  required
                />
                <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', marginTop: 4, display: 'block' }}>
                  You can login using your email address or full name
                </small>
              </div>

              <div className="form-group">
                <label className="form-label" htmlFor="password">Password</label>
                <div style={{ position: 'relative' }}>
                  <input
                    type={showPassword ? 'text' : 'password'}
                    className="form-control"
                    id="password"
                    placeholder="Enter your password"
                    value={loginState.password}
                    onChange={(event) => setLoginState((prev) => ({ ...prev, password: event.target.value }))}
                    required
                  />
                  <button
                    type="button"
                    className="toggle-pw"
                    onClick={() => setShowPassword((prev) => !prev)}
                    style={{ position: 'absolute', right: 12, top: '50%', transform: 'translateY(-50%)', background: 'none', border: 'none', color: 'var(--text-dim)', cursor: 'pointer' }}
                  >
                    <i className={`fas ${showPassword ? 'fa-eye-slash' : 'fa-eye'}`}></i>
                  </button>
                </div>
              </div>

              {loginState.error ? (
                <div className="flash flash-error" style={{ marginBottom: 14 }}>
                  <i className="fas fa-times-circle"></i>
                  <span>{loginState.error}</span>
                </div>
              ) : null}

              <button
                type="submit"
                className="btn btn-primary"
                style={{ marginTop: 8 }}
                disabled={loginState.loading}
              >
                <i className={`fas ${loginState.loading ? 'fa-spinner fa-spin' : 'fa-sign-in-alt'}`}></i>{' '}
                {loginState.loading ? 'Signing In...' : 'Sign In'}
              </button>
              {bootstrap?.authUi?.standardOtpLoginEnabled ? (
                <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', marginTop: 8, display: 'block' }}>
                  After sign in, an OTP will be sent to your registered email.
                </small>
              ) : null}

              {bootstrap?.authUi?.googleOauthEnabled ? (
                <>
                  <div style={{ display: 'flex', alignItems: 'center', gap: 10, margin: '16px 0 12px' }}>
                    <div style={{ flex: 1, height: 1, background: 'var(--border)' }}></div>
                    <span style={{ fontSize: '.76rem', color: 'var(--text-dim)', textTransform: 'uppercase', letterSpacing: '.08em' }}>or</span>
                    <div style={{ flex: 1, height: 1, background: 'var(--border)' }}></div>
                  </div>
                  <button
                    type="button"
                    className="btn btn-outline"
                    style={{ width: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', gap: 8 }}
                    onClick={handleGoogleLoginStart}
                  >
                    <i className="fab fa-google"></i> Sign in with Google
                  </button>
                </>
              ) : null}

              {bootstrap?.authUi?.forgotPasswordEnabled ? (
                <div style={{ marginTop: 10, textAlign: 'center' }}>
                  <button
                    type="button"
                    className="btn btn-outline"
                    style={{ width: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', gap: 8 }}
                    onClick={() => setForgotPasswordState((prev) => ({ ...prev, open: true, stage: 'request', error: '', identifier: loginState.identifier || prev.identifier }))}
                  >
                    <i className="fas fa-key"></i> Forgot Password
                  </button>
                </div>
              ) : null}

            </form>
          )}

          <div style={{ marginTop: 24, textAlign: 'center' }}>
            <p style={{ fontSize: '.78rem', color: 'var(--text-muted)' }}>
              RMK CET Department of Science and Humanities. All rights reserved.
            </p>
          </div>
        </div>
      </main>
      {loginConflictInfoOpen ? (
        <div className="modal-overlay open" onClick={() => setLoginConflictInfoOpen(false)}>
          <div className="modal" style={{ maxWidth: 440 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-circle-info"></i> Session Details Unavailable</h3>
              <button className="modal-close" type="button" onClick={() => setLoginConflictInfoOpen(false)}>
                <i className="fas fa-times"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>
              We detected another active Google sign-in for this account, but that session did not expose browser or device details.
            </p>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 18 }}>
              If you continue, SHINE will still log out that active session and sign you in here safely.
            </p>
            <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
              <button type="button" className="btn btn-primary" onClick={() => setLoginConflictInfoOpen(false)}>
                Understood
              </button>
            </div>
          </div>
        </div>
      ) : null}
      {sessionEndNotice ? (
        <div className="modal-overlay open" onClick={() => setSessionEndNotice(null)}>
          <div className="modal" style={{ maxWidth: 440 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-circle-info"></i> {sessionEndNotice.title || 'Logged Out'}</h3>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 18 }}>
              {sessionEndNotice.message}
            </p>
            <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
              <button type="button" className="btn btn-primary" onClick={() => setSessionEndNotice(null)}>
                OK
              </button>
            </div>
          </div>
        </div>
      ) : null}
      {forgotPasswordState.open ? (
        <div
          className="modal-overlay open"
          onClick={() => {
            if (forgotPasswordState.loading) return;
            closeForgotPasswordModal();
          }}
        >
          <div className="modal" style={{ maxWidth: 480 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-key"></i> Forgot Password</h3>
              <button
                className="modal-close"
                type="button"
                onClick={closeForgotPasswordModal}
                disabled={forgotPasswordState.loading}
              >
                <i className="fas fa-xmark"></i>
              </button>
            </div>

            {forgotPasswordState.stage === 'request' ? (
              <form onSubmit={(event) => void handleForgotPasswordRequest(event)} autoComplete="off">
                <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 14 }}>
                  Enter your email or full name. We&apos;ll send a password reset OTP to your registered email address.
                </p>
                <div className="form-group">
                  <label className="form-label">Email or Name</label>
                  <input
                    className="form-control"
                    autoComplete="off"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.identifier}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, identifier: event.target.value }))}
                    placeholder="Enter your email or full name"
                    required
                    autoFocus
                  />
                </div>
                {forgotPasswordState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{forgotPasswordState.error}</span>
                  </div>
                ) : null}
                <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={closeForgotPasswordModal}
                    disabled={forgotPasswordState.loading}
                  >
                    Cancel
                  </button>
                  <button type="submit" className="btn btn-primary btn-sm" disabled={forgotPasswordState.loading}>
                    <i className={`fas ${forgotPasswordState.loading ? 'fa-spinner fa-spin' : 'fa-paper-plane'}`}></i>
                    {forgotPasswordState.loading ? 'Sending...' : 'Send OTP'}
                  </button>
                </div>
              </form>
            ) : null}

            {forgotPasswordState.stage === 'verify' ? (
              <form onSubmit={(event) => void handleForgotPasswordVerify(event)} autoComplete="off">
                <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 14 }}>
                  OTP sent to {forgotPasswordState.maskedEmail || 'your email'}.
                </p>
                <div className="form-group">
                  <label className="form-label">Reset OTP</label>
                  <input
                    className="form-control otp-code-input"
                    autoComplete="off"
                    inputMode="numeric"
                    pattern="\d{6}"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.otp_code}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, otp_code: normalizeOtpCode(event.target.value) }))}
                    placeholder="Enter 6-digit OTP"
                    minLength={6}
                    maxLength={6}
                    required
                    autoFocus
                  />
                </div>
                {forgotPasswordState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{forgotPasswordState.error}</span>
                  </div>
                ) : null}
                <div className="btn-group" style={{ justifyContent: 'space-between' }}>
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => setForgotPasswordState((prev) => ({
                      ...prev,
                      stage: 'request',
                      otp_code: '',
                      error: '',
                      loading: false,
                    }))}
                    disabled={forgotPasswordState.loading}
                  >
                    <i className="fas fa-arrow-left"></i> Back
                  </button>
                  <button type="submit" className="btn btn-primary btn-sm" disabled={forgotPasswordState.loading}>
                    <i className={`fas ${forgotPasswordState.loading ? 'fa-spinner fa-spin' : 'fa-shield-halved'}`}></i>
                    {forgotPasswordState.loading ? 'Verifying...' : 'Verify OTP'}
                  </button>
                </div>
              </form>
            ) : null}

            {forgotPasswordState.stage === 'reset' ? (
              <form onSubmit={(event) => void handleForgotPasswordComplete(event)} autoComplete="off">
                <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 14 }}>
                  Set a new password for {forgotPasswordState.maskedEmail || 'your account'}.
                </p>
                <div className="form-group">
                  <label className="form-label">New Password</label>
                  <input
                    className="form-control"
                    type="password"
                    autoComplete="new-password"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.new_password}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, new_password: event.target.value }))}
                    placeholder="Enter new password"
                    required
                    autoFocus
                  />
                </div>
                <div className="form-group">
                  <label className="form-label">Confirm Password</label>
                  <input
                    className="form-control"
                    type="password"
                    autoComplete="new-password"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.confirm_password}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, confirm_password: event.target.value }))}
                    placeholder="Re-enter new password"
                    required
                  />
                </div>
                {forgotPasswordState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{forgotPasswordState.error}</span>
                  </div>
                ) : null}
                <div className="btn-group" style={{ justifyContent: 'space-between' }}>
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => setForgotPasswordState((prev) => ({
                      ...prev,
                      stage: 'verify',
                      new_password: '',
                      confirm_password: '',
                      error: '',
                      loading: false,
                    }))}
                    disabled={forgotPasswordState.loading}
                  >
                    <i className="fas fa-arrow-left"></i> Back
                  </button>
                  <button type="submit" className="btn btn-primary btn-sm" disabled={forgotPasswordState.loading}>
                    <i className={`fas ${forgotPasswordState.loading ? 'fa-spinner fa-spin' : 'fa-key'}`}></i>
                    {forgotPasswordState.loading ? 'Updating...' : 'Reset Password'}
                  </button>
                </div>
              </form>
            ) : null}
          </div>
        </div>
      ) : null}
      </>
    );
  }

  const renderDesktopAppSettingsPanel = () => (
    <div className="card mb-3" style={{ maxWidth: 1120 }}>
      <div className="card-title"><i className="fas fa-desktop"></i> Desktop App Settings</div>
      {!runtimeConfig.isDesktop ? (
        <div className="panel-placeholder">Desktop settings are available inside the Windows app.</div>
      ) : (
        <>
          <div className="detail-display-panel" style={{ marginBottom: 14 }}>
            <div className="detail-display-grid">
              <div><div className="detail-display-label">Server Status</div><div className="detail-display-value is-strong">{desktopConnectivity?.online ? 'Online' : 'Recovery Mode'}</div></div>
              <div><div className="detail-display-label">App Version</div><div className="detail-display-value">{runtimeConfig.appVersion || '-'}</div></div>
            </div>
          </div>
          {desktopConnectivity?.error ? <div className="alert alert-warning" style={{ marginBottom: 14 }}>{desktopConnectivity.error}</div> : null}
          {[
            ['launchAtWindowsStartup', 'Start With Windows', 'Launch Shine into the tray on login.'],
            ['startMinimizedToTrayOnLogin', 'Startup Minimized To Tray', 'Keep startup quiet until the app is opened manually.'],
            ['minimizeToTrayOnClose', 'Close Minimizes To Tray', 'Use the tray Quit action to fully exit.'],
            ['desktopNotificationsEnabled', 'Desktop Notifications', 'Show update and counselor alert notifications.'],
            ...(currentUser?.role === 'admin'
              ? [
                ['updateChecksEnabled', 'Update Checks', 'Check the hosted desktop release channel.'],
                ['autoInstallUpdatesWhenIdle', 'Install Updates When Idle', 'Defer installs while marks or notice sending is open.'],
              ]
              : []),
          ].map(([key, label, detail]) => (
            <div className="settings-slider-row" key={key}>
              <div><div className="form-label">{label}</div><div className="inline-muted">{detail}</div></div>
              <label className="settings-slider">
                <input
                  type="checkbox"
                  checked={Boolean(desktopAppSettings?.[key as keyof DesktopAppSettings])}
                  disabled={desktopSettingsSaving}
                  onChange={(event) => {
                    const nextValue = event.target.checked;
                    setDesktopAppSettings((prev) => prev ? { ...prev, [key]: nextValue } : prev);
                    void saveDesktopSettingPatch({ [key]: nextValue } as Partial<DesktopAppSettings>);
                  }}
                />
                <span className="settings-slider-track" aria-hidden="true"></span>
              </label>
            </div>
          ))}
          {(currentUser?.role === 'hod' || currentUser?.role === 'principal') ? (
            <div className="card mt-3" style={{ padding: 14, background: 'rgba(148,163,184,.055)', border: '1px solid var(--border)' }}>
              <div className="card-title" style={{ fontSize: '.92rem', marginBottom: 10 }}><i className="fas fa-list-check"></i> Pending Counselor Digest</div>
              <div className="form-row">
                <div className="form-group" style={{ maxWidth: 220 }}>
                  <label className="form-label">Digest Day</label>
                  <select
                    className="form-control"
                    value={desktopAppSettings?.higherOfficialDigestDay || 'monday'}
                    onChange={(event) => {
                      const nextValue = event.target.value;
                      setDesktopAppSettings((prev) => prev ? { ...prev, higherOfficialDigestDay: nextValue } : prev);
                      void saveDesktopSettingPatch({ higherOfficialDigestDay: nextValue } as Partial<DesktopAppSettings>);
                    }}
                  >
                    {['monday', 'tuesday', 'wednesday', 'thursday', 'friday', 'saturday', 'sunday'].map((day) => (
                      <option key={day} value={day}>{day[0].toUpperCase() + day.slice(1)}</option>
                    ))}
                  </select>
                </div>
                <div className="form-group" style={{ maxWidth: 220 }}>
                  <label className="form-label">Digest Scope</label>
                  <select
                    className="form-control"
                    value={desktopAppSettings?.higherOfficialDigestScope || 'allocated'}
                    onChange={(event) => {
                      const nextValue = event.target.value === 'all' ? 'all' : 'allocated';
                      setDesktopAppSettings((prev) => prev ? { ...prev, higherOfficialDigestScope: nextValue } : prev);
                      void saveDesktopSettingPatch({ higherOfficialDigestScope: nextValue } as Partial<DesktopAppSettings>);
                    }}
                  >
                    <option value="allocated">Allocated Scope</option>
                    <option value="all">All</option>
                  </select>
                </div>
              </div>
            </div>
          ) : null}
          {desktopUpdateInfo ? <div className="ui-preview-note" style={{ marginTop: 14 }}>Update status: {desktopUpdateInfo.available ? `Version ${desktopUpdateInfo.version} available` : (desktopUpdateInfo.error || 'No update available')}</div> : null}
          <div className="btn-group" style={{ marginTop: 14 }}>
            <button type="button" className="btn btn-outline" onClick={() => void loadDesktopRuntimeState()}><i className="fas fa-rotate"></i> Refresh Status</button>
            {currentUser?.role === 'admin' ? (
              <>
                <button type="button" className="btn btn-outline" disabled={desktopUpdateChecking} onClick={() => void handleDesktopUpdateCheck()}><i className={`fas ${desktopUpdateChecking ? 'fa-spinner fa-spin' : 'fa-cloud-arrow-down'}`}></i> {desktopUpdateChecking ? 'Checking...' : 'Check Updates'}</button>
                {desktopUpdateInfo?.available ? <button type="button" className="btn btn-warning" onClick={() => void handleDesktopUpdateInstall()}><i className="fas fa-download"></i> Install Update</button> : null}
              </>
            ) : null}
          </div>
        </>
      )}
    </div>
  );

  const renderNotificationCenterPage = () => (
    <section className="notification-page">
      <div className="card mb-3">
        <div className="notification-page-header">
          <button type="button" className="btn btn-outline btn-sm" onClick={() => setNotificationCenterOpen(false)}>
            <i className="fas fa-arrow-left"></i> Back
          </button>
          <div>
            <div className="card-title" style={{ marginBottom: 2 }}><i className="fas fa-bell"></i> Notification Center</div>
            <div className="inline-muted">{unreadNotificationCount} unread notification{unreadNotificationCount === 1 ? '' : 's'}</div>
          </div>
          {appNotifications.length ? (
            <button type="button" className="btn btn-outline btn-sm" onClick={() => markNotificationsRead(appNotifications.map((item) => item.key))}>
              <i className="fas fa-check-double"></i> Mark All Read
            </button>
          ) : null}
        </div>
      </div>
      {appNotifications.length ? (
        <div className="notification-page-list">
          {appNotifications.map((item) => {
            const unread = !seenNotificationKeys.has(item.key);
            return (
              <article key={item.key} className={`notification-page-item ${unread ? 'unread' : ''} notification-${item.severity}`}>
                <button
                  type="button"
                  className="notification-page-main"
                  onClick={() => {
                    markNotificationsRead([item.key]);
                    if (item.actionTab) {
                      setActiveTab(item.actionTab);
                      setNotificationCenterOpen(false);
                    }
                  }}
                >
                  <span className="notification-dot" aria-hidden="true"></span>
                  <span className="notification-content">
                    <strong>{item.title}</strong>
                    <span>{item.body}</span>
                    {item.createdAt ? <small>{formatUtcSqlDateTime(item.createdAt)}</small> : null}
                  </span>
                </button>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => deleteNotifications([item.key])}>
                  <i className="fas fa-trash"></i> Delete
                </button>
              </article>
            );
          })}
        </div>
      ) : (
        <div className="card"><div className="panel-placeholder">No notifications right now.</div></div>
      )}
    </section>
  );

  return (
    <>
      <aside className={`sidebar ${mobileSidebarOpen ? 'open' : ''} ${embeddedWhatsappSidepaneLayoutActive ? 'embed-sidepanel-sidebar' : ''}`} id="sidebar">
        <div className="sidebar-header">
          <button className="sidebar-close" type="button" aria-label="Close navigation" onClick={() => setMobileSidebarOpen(false)}>
            <i className="fas fa-xmark"></i>
          </button>
          <div className="logo-area">
            <div className="logo-image" role="img" aria-label="RMKCET SHINE Logo"></div>
            <div className="logo-text">
              <span className="logo-subtitle-main">S&amp;H Internal Notification Engine</span>
            </div>
          </div>
        </div>

        <nav className="sidebar-nav">
          {navTabs.map((tab) => (
            <button
              key={tab}
              type="button"
              className={`nav-link tab-nav ${activeTab === tab ? 'active' : ''}`}
              onClick={() => handleSidebarTabNavigation(tab)}
              style={{ width: '100%', border: 'none', background: activeTab === tab ? undefined : 'transparent', textAlign: 'left', fontFamily: 'inherit', fontSize: 'inherit' }}
            >
              <i className={`fas ${getNavIcon(tab)}`}></i><span>{getNavLabel(tab, currentUser)}</span>
            </button>
          ))}
        </nav>

        <div className="sidebar-footer">
          <div className="user-info">
            <div className="user-avatar">{currentUser.name[0] || '?'}</div>
            <div className="user-details">
              <div className="user-name-row">
                <span className="user-name">{currentUser.name}</span>
                {canSwitchRoles ? (
                  <button
                    type="button"
                    className="btn btn-outline btn-sm icon-btn role-switch-icon-btn"
                    onClick={handleOpenRoleSwitchModal}
                    title="Change role"
                    aria-label="Change role"
                  >
                    <i className="fas fa-right-left"></i>
                  </button>
                ) : null}
              </div>
              <span className="user-role">{getRoleBadgeLabel(currentUser)}</span>
            </div>
          </div>
          {sidebarDepartmentCodes.length ? (
            <div className="user-department-list user-department-strip">
              {sidebarDepartmentCodes.map((departmentCode) => (
                <span className="user-department-chip is-active" key={departmentCode}>
                  <span className="user-department-dot"></span>{departmentCode}
                </span>
              ))}
            </div>
          ) : null}
          <button
            type="button"
            className={(isTestMode || archiveViewActive) ? 'logout-btn test-mode-btn' : 'logout-btn'}
            onClick={() => void handleLogout()}
          >
            <i className={`fas ${isTestMode || archiveViewActive ? 'fa-door-open' : 'fa-sign-out-alt'}`}></i> {isTestMode ? 'Exit Test Mode' : archiveViewActive ? 'Exit Archive View' : 'Logout'}
          </button>
        </div>
      </aside>
      {mobileSidebarOpen ? <div className="sidebar-overlay" onClick={() => setMobileSidebarOpen(false)}></div> : null}

      <main className={`main-content ${embeddedWhatsappSidepaneLayoutActive ? 'embed-sidepanel-active' : ''} ${desktopWhatsappWorkspaceExiting ? 'embed-sidepanel-exiting' : ''}`} id="mainContent" ref={mainContentRef}>
        <header className={`top-header ${embeddedWhatsappSidepaneLayoutActive ? 'embed-sidepanel-header' : ''} ${desktopWhatsappWorkspaceExiting ? 'embed-sidepanel-header-exiting' : ''}`}>
          {embeddedWhatsappSidepaneLayoutActive ? null : (
            <button className="mobile-toggle" type="button" onClick={() => setMobileSidebarOpen(true)}><i className="fas fa-bars"></i></button>
          )}
          <h1 className="page-title">{notificationCenterOpen ? 'Notification Center' : getPageTitle(activeTab, currentUser)}</h1>
          <div className="header-actions">
            <div className="icon-group">
              {archiveViewActive ? (
                <span className="header-badge" style={{ color: 'var(--warning)', borderColor: 'rgba(245,158,11,.35)', background: 'rgba(245,158,11,.12)' }}>
                  <i className="fas fa-eye"></i> Archive {bootstrap?.archiveView?.academicYear || bootstrap?.archiveView?.archiveName}
                </span>
              ) : null}
              {embeddedWhatsappSidepaneLayoutActive ? (
                <button
                  type="button"
                  className="btn btn-outline btn-sm icon-btn"
                  onClick={() => void hideDesktopWhatsappWorkspace()}
                >
                  <i className="fas fa-arrow-left"></i>
                  <span>Back To Template</span>
                </button>
              ) : null}
              {currentUser.role === 'admin' ? (
                <button
                  className={`btn btn-outline btn-sm icon-btn smtp-status-btn smtp-${smtpIndicator.state}`}
                  type="button"
                  title={smtpIndicator.detail}
                  onClick={() => {
                    setActiveTab('config');
                    void loadConfigOverview();
                  }}
                >
                  <i className={`fas ${smtpIndicator.icon}`}></i>
                  <span>{smtpIndicator.label}</span>
                </button>
              ) : null}
              <button className="btn btn-outline btn-sm icon-btn" type="button" title="Toggle theme" onClick={() => setTheme((prev) => (prev === 'light' ? 'dark' : 'light'))}>
                <i className={`fas ${theme === 'light' ? 'fa-moon' : 'fa-sun'}`}></i>
                <span>Theme</span>
              </button>
              <button
                className="btn btn-outline btn-sm icon-btn notification-center-btn"
                type="button"
                title="Notification Center"
                onClick={openNotificationCenter}
              >
                <i className="fas fa-bell"></i>
                <span>Notifications</span>
                {unreadNotificationCount > 0 ? <span className="notification-count-badge">{unreadNotificationCount}</span> : null}
              </button>
              {!embeddedWhatsappSidepaneLayoutActive ? (
                <button
                  type="button"
                  className="btn btn-outline btn-sm icon-btn"
                  onClick={() => {
                    setSelfPasswordModalOpen(true);
                    setSelfPasswordDraft({
                      current_password: '',
                      otp_code: '',
                      new_password: '',
                      confirm_password: '',
                    });
                    setSelfPasswordOtpSentTo('');
                  }}
                >
                  <i className="fas fa-key"></i>
                  <span>Reset Password</span>
                </button>
              ) : null}
              {currentUser.role === 'admin' ? (
                <button
                  type="button"
                  className="btn btn-outline btn-sm icon-btn"
                  onClick={() => {
                    setActiveTab('config');
                    void loadConfigOverview();
                  }}
                >
                  <i className="fas fa-cog"></i>
                  <span>Settings</span>
                </button>
              ) : runtimeConfig.isDesktop ? (
                <button
                  type="button"
                  className="btn btn-outline btn-sm icon-btn"
                  onClick={() => {
                    setDesktopSettingsPanelOpen(true);
                    void loadDesktopRuntimeState();
                    openDesktopSettings();
                  }}
                >
                  <i className="fas fa-cog"></i>
                  <span>Settings</span>
                </button>
              ) : null}
              {archiveViewActive ? (
                <button className="btn btn-outline btn-sm icon-btn" type="button" onClick={() => void handleExitArchiveView()}>
                  <i className="fas fa-arrow-right-from-bracket"></i>
                  <span>Exit View</span>
                </button>
              ) : null}
            </div>
            <span className="header-badge desktop-only"><i className="fas fa-clock"></i> {bootstrap?.nowLabel}</span>
          </div>
        </header>

        {flash ? (
          <div className="flash-toast-container" role="status" aria-live="polite">
            <div className={`flash flash-toast flash-${flash.type}`}>
              <i className={`fas ${flash.type === 'success' ? 'fa-check-circle' : flash.type === 'warning' ? 'fa-exclamation-triangle' : flash.type === 'error' ? 'fa-times-circle' : 'fa-info-circle'}`}></i>
              <span>{flash.message}</span>
              <button className="flash-close" onClick={() => setFlash(null)}><i className="fas fa-times"></i></button>
            </div>
          </div>
        ) : null}
        {desktopWhatsappWorkspaceTransition ? (
          <div className={`desktop-embed-transition-overlay ${desktopWhatsappWorkspaceTransition === 'exit' ? 'is-exit' : ''}`} role="status" aria-live="polite">
            <div className="desktop-embed-transition-card">
              <div className="spinner-ring"></div>
              <div className="desktop-embed-transition-title">
                {desktopWhatsappWorkspaceTransition === 'enter' ? 'Opening WhatsApp workspace' : 'Returning to template'}
              </div>
              <div className="desktop-embed-transition-copy">
                {desktopWhatsappWorkspaceTransition === 'enter'
                  ? 'Preparing the split send workspace.'
                  : 'Closing the compact send queue.'}
              </div>
            </div>
          </div>
        ) : null}

        <div className={`content-area ${embeddedWhatsappSidepaneLayoutActive ? 'embed-sidepanel-content' : ''} ${desktopWhatsappWorkspaceExiting ? 'embed-sidepanel-content-exiting' : ''}`} ref={contentAreaRef}>
          {notificationCenterOpen ? (
            renderNotificationCenterPage()
          ) : currentUser.role === 'counselor' && activeTab === 'test-database' && counselorSendVerify ? (
            <>
              <div className="report-sticky-toolbar mb-2">
                <div className="report-toolbar-balanced">
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => setCounselorSendVerify(null)}
                  >
                    <i className="fas fa-arrow-left"></i> Back To Reports
                  </button>
                  <div className="report-toolbar-center">
                    <span className="badge badge-info">{counselorSendVerify.testName || 'Selected Test'}</span>
                  </div>
                  <div></div>
                </div>
              </div>

              <div className="card" style={{ maxWidth: 780 }}>
                <div className="card-title"><i className="fab fa-whatsapp"></i> WhatsApp App Verification</div>
                <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                  We are checking whether the WhatsApp app is available on this device. This takes about 5 seconds.
                </p>

                <div
                  className="card"
                  style={{
                    padding: 12,
                    border: `1px solid ${
                      counselorSendVerify.tone === 'success'
                        ? 'rgba(34,197,94,.35)'
                        : counselorSendVerify.tone === 'error'
                          ? 'rgba(239,68,68,.35)'
                          : 'var(--border)'
                    }`,
                    background: 'var(--bg-input)',
                  }}
                >
                  <strong>{counselorSendVerify.title}</strong>
                  <div style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginTop: 6 }}>{counselorSendVerify.body}</div>
                </div>

                {counselorSendVerify.appFound ? (
                  <div style={{ display: 'flex', gap: 10, flexWrap: 'wrap', marginTop: 14 }}>
                    <button type="button" className="btn btn-success" onClick={() => void openCounselorSendPage(counselorSendVerify.testId, 'app')}>
                      <i className="fas fa-check"></i> Continue (WhatsApp App)
                    </button>
                    <button type="button" className="btn btn-outline" onClick={() => void openCounselorSendPage(counselorSendVerify.testId, 'web')}>
                      <i className="fas fa-globe"></i> Use WhatsApp Web
                    </button>
                  </div>
                ) : null}

                {counselorSendVerify.completed && !counselorSendVerify.appFound ? (
                  <div style={{ display: 'flex', gap: 10, flexWrap: 'wrap', marginTop: 14 }}>
                    <button type="button" className="btn btn-primary" onClick={() => installWhatsappAndReturn()}>
                      <i className="fas fa-download"></i> Install WhatsApp App And Continue
                    </button>
                    <button type="button" className="btn btn-outline" onClick={() => void openCounselorSendPage(counselorSendVerify.testId, 'web')}>
                      <i className="fas fa-globe"></i> Use WhatsApp Web
                    </button>
                  </div>
                ) : null}
              </div>
            </>
          ) : currentUser.role === 'counselor' && activeTab === 'test-database' && (counselorSendLoading || counselorSendPage) ? (
            counselorSendLoading ? (
              <div className="card">
                <div className="panel-placeholder">Loading send results...</div>
              </div>
            ) : counselorSendPage ? (
              <>
                {!embeddedWhatsappSidepaneLayoutActive ? (
                  <div className="report-sticky-toolbar mb-2">
                    <div className="report-toolbar-balanced">
                      <button
                        type="button"
                        className="btn btn-outline btn-sm"
                        onClick={() => {
                          stopCounselorBatchSend();
                          void stopDesktopWhatsappWorkspaceImmediate();
                          setCounselorSendPage(null);
                        }}
                      >
                        <i className="fas fa-arrow-left"></i> Back To Reports
                      </button>
                      <div className="report-toolbar-center">
                        <span className="badge badge-info">{counselorSendPage.meta.test_name || 'Selected Test'}</span>
                      </div>
                      <div></div>
                    </div>
                  </div>
                ) : null}

                {counselorSendEmbeddedWhatsappActive ? (
                  <div
                    className={`desktop-send-workspace-layout ${embeddedWhatsappSidepaneLayoutActive ? 'is-compact' : ''}`}
                    ref={desktopReportWorkspaceRef}
                  >
                    <div className="desktop-send-workspace-main">
                      <div className="card mb-3">
                        <div className="card-title"><i className="fas fa-sliders"></i> Common Variables</div>
                        <div className="form-row">
                          <div className="form-group">
                            <label className="form-label">Test</label>
                            <input
                              className="form-control"
                              defaultValue={counselorSendVars.test_name}
                              onChange={(event) => { counselorSendVarsRef.current = { ...counselorSendVarsRef.current, test_name: event.target.value }; }}
                              onBlur={() => setCounselorSendVars((prev) => ({ ...prev, test_name: counselorSendVarsRef.current.test_name }))}
                            />
                          </div>
                          <div className="form-group">
                            <label className="form-label">Semester</label>
                            <input
                              className="form-control"
                              defaultValue={counselorSendVars.semester}
                              onChange={(event) => { counselorSendVarsRef.current = { ...counselorSendVarsRef.current, semester: event.target.value }; }}
                              onBlur={() => setCounselorSendVars((prev) => ({ ...prev, semester: counselorSendVarsRef.current.semester }))}
                            />
                          </div>
                        </div>
                        <div className="form-row">
                          <div className="form-group">
                            <label className="form-label">Batch</label>
                            <input
                              className="form-control"
                              defaultValue={counselorSendVars.batch_name}
                              onChange={(event) => { counselorSendVarsRef.current = { ...counselorSendVarsRef.current, batch_name: event.target.value }; }}
                              onBlur={() => setCounselorSendVars((prev) => ({ ...prev, batch_name: counselorSendVarsRef.current.batch_name }))}
                            />
                          </div>
                          <div className="form-group">
                            <label className="form-label">Send Mode</label>
                            <div className="segmented-switch send-mode-switch" data-count={2} data-mode={counselorSendVars.sendMode === 'embed' ? 'app' : counselorSendVars.sendMode}>
                              <div className="segmented-switch-thumb" aria-hidden="true"></div>
                              <button
                                type="button"
                                className={`segmented-switch-option ${counselorSendVars.sendMode === 'app' || counselorSendVars.sendMode === 'embed' ? 'active' : ''}`}
                                onClick={() => void handleCounselorSendModeChange('app')}
                              >
                                App
                              </button>
                              <button
                                type="button"
                                className={`segmented-switch-option ${counselorSendVars.sendMode === 'web' ? 'active' : ''}`}
                                onClick={() => void handleCounselorSendModeChange('web')}
                              >
                                Web
                              </button>
                            </div>
                            <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', display: 'block', marginTop: 6 }}>
                              {counselorSendVars.sendMode === 'web'
                                  ? 'Web mode keeps the normal WhatsApp Web flow.'
                                  : 'App mode opens the floating student list after you start the workflow.'}
                            </small>
                          </div>
                        </div>
                        <div className="form-group">
                          <label className="form-label">Message Template</label>
                          <textarea
                            className="form-control"
                            rows={8}
                            defaultValue={counselorSendVars.template}
                            onChange={(event) => { counselorSendVarsRef.current = { ...counselorSendVarsRef.current, template: event.target.value }; }}
                            onBlur={() => setCounselorSendVars((prev) => ({ ...prev, template: counselorSendVarsRef.current.template }))}
                          />
                        </div>
                        <div className="form-group" style={{ marginTop: 14 }}>
                          <label className="form-label">Subject/Metric Order for Message</label>
                          <div className="text-muted" style={{ fontSize: '.82rem', marginBottom: 8 }}>
                            Arrange subject order for message body. Pending: {counselorSendRowCounts.pending}, Generated: {counselorSendRowCounts.generated}.
                          </div>
                          <div className="field-order-list">
                            {counselorFieldOrder.map((entry, index) => (
                              <div key={`${entry.type}-${entry.type === 'subject' ? entry.normalizedKey : entry.metricKey}`} className="field-order-tab">
                                <div className="field-order-tab-label">{entry.label}</div>
                                <div className="field-order-tab-actions">
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => moveCounselorFieldOrder(index, -1)} disabled={index === 0}>
                                    <i className="fas fa-arrow-up"></i>
                                  </button>
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => moveCounselorFieldOrder(index, 1)} disabled={index === counselorFieldOrder.length - 1}>
                                    <i className="fas fa-arrow-down"></i>
                                  </button>
                                </div>
                              </div>
                            ))}
                          </div>
                          <div className="btn-group mt-1">
                            <button type="button" className="btn btn-outline btn-sm" onClick={() => setCounselorFieldOrder(counselorDefaultFieldOrder.map((item) => ({ ...item })))}>
                              <i className="fas fa-rotate-left"></i> Reset Default Order
                            </button>
                          </div>
                        </div>
                        {(counselorSendVars.sendMode === 'app' || counselorSendVars.sendMode === 'web' || counselorSendVars.sendMode === 'embed') && !desktopWhatsappWorkspaceStarted ? (
                          <div className="desktop-send-template-footer">
                            <button
                              type="button"
                              className="btn btn-success desktop-send-start-btn"
                              disabled={desktopWhatsappWorkspaceBusy}
                              onClick={() => void startDesktopWhatsappWorkspace('report')}
                            >
                              <i className={`fas ${desktopWhatsappWorkspaceBusy ? 'fa-spinner fa-spin' : 'fa-play'}`}></i> {desktopWhatsappWorkspaceBusy ? 'Opening...' : 'Start Workflow'}
                            </button>
                          </div>
                        ) : null}
                      </div>

                      {counselorSendDesktopWorkspaceMode ? (
                        <div className="desktop-send-lite-summary">
                          <span className="badge badge-info">{counselorSendRowCounts.total} students loaded</span>
                          <span className="badge badge-warning">{counselorSendRowCounts.pending} pending</span>
                          <span className="badge badge-success">{counselorSendRowCounts.generated} generated</span>
                        </div>
                      ) : (
                        <div className="table-wrapper table-scroll-lg">
                          <table className="sticky-table">
                            <thead>
                              <tr>
                                <th>Reg No</th>
                                <th>Name</th>
                                <th>Phone</th>
                                <th>Status</th>
                                <th>Action</th>
                              </tr>
                            </thead>
                            <tbody>
                              {counselorSendPage.rows.length ? counselorSendPage.rows.map((row) => (
                                <tr key={row.reg_no}>
                                  <td><strong>{row.reg_no}</strong></td>
                                  <td>{row.student_name}</td>
                                  <td>{row.parent_phone || '-'}</td>
                                  <td>
                                    <span className={`badge ${row.status === 'Generated' ? 'badge-success' : 'badge-warning'}`}>{row.status}</span>
                                  </td>
                                  <td>
                                    <button
                                      type="button"
                                      className={`btn btn-primary btn-sm ${row.status === 'Generated' ? 'send-btn-generated' : ''}`}
                                      onClick={() => void handleCounselorSendSingle(row)}
                                    >
                                      <i className="fab fa-whatsapp"></i> Send To WhatsApp
                                    </button>
                                  </td>
                                </tr>
                              )) : (
                                <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 18 }}>No students available for this test.</td></tr>
                              )}
                            </tbody>
                          </table>
                        </div>
                      )}
                    </div>

                    {embeddedWhatsappSidepaneLayoutActive && counselorSendDesktopWorkspaceMode ? (
                    <aside className="desktop-send-workspace-pane">
                      <div className="desktop-send-sidepane-panel">
                        <div className={`desktop-send-student-list-shell ${desktopWhatsappWorkspaceExiting ? 'is-exiting' : ''}`} ref={desktopReportQueueShellRef}>
                          <div className="card-title"><i className="fas fa-user-group"></i> Student Send List</div>
                          {desktopWhatsappWorkspaceBusy ? (
                            <div className="desktop-send-workspace-loader">
                              <div className="spinner-ring" aria-hidden="true"></div>
                              <div className="desktop-send-workspace-loader-copy">Preparing WhatsApp workspace...</div>
                            </div>
                          ) : (
                            <div className="desktop-send-student-list">
                              {counselorSendPage.rows.length ? counselorSendPage.rows.map((row) => (
                                <div
                                  key={row.reg_no}
                                  className={`desktop-send-student-item ${row.status === 'Generated' ? 'is-generated' : ''} ${desktopWhatsappActiveTarget?.kind === 'report' && desktopWhatsappActiveTarget.regNo === row.reg_no ? 'is-active' : ''}`}
                                >
                                  <div className="desktop-send-student-main">
                                  <div className="desktop-send-student-name">{row.student_name}</div>
                                    {desktopWhatsappActiveTarget?.kind === 'report' && desktopWhatsappActiveTarget.regNo === row.reg_no ? null : desktopReportQueueState[row.reg_no] ? (
                                      <span className="desktop-send-student-active">{desktopReportQueueState[row.reg_no].toUpperCase()}</span>
                                    ) : null}
                                  </div>
                                  <button
                                    type="button"
                                    className={`btn btn-primary btn-sm desktop-send-student-button ${row.status === 'Generated' ? 'send-btn-generated' : ''}`}
                                    disabled={desktopWhatsappLoadingRow === row.reg_no}
                                    onClick={() => void handleCounselorDesktopQueuePick(row)}
                                  >
                                    <i className={desktopWhatsappLoadingRow === row.reg_no ? 'fas fa-spinner fa-spin' : 'fab fa-whatsapp'}></i> {desktopWhatsappLoadingRow === row.reg_no ? 'Opening...' : 'Send To WhatsApp'}
                                  </button>
                                </div>
                              )) : (
                                <div className="text-muted" style={{ fontSize: '.84rem' }}>No students available for this test.</div>
                              )}
                            </div>
                          )}
                        </div>
                      </div>
                    </aside>
                    ) : null}
                  </div>
                ) : (
                <>
                <div className="card mb-3">
                  <div className="card-title"><i className="fas fa-sliders"></i> Common Variables</div>
                  <div className="form-row">
                    <div className="form-group">
                      <label className="form-label">Test</label>
                      <input className="form-control" value={counselorSendVars.test_name} onChange={(event) => setCounselorSendVars((prev) => ({ ...prev, test_name: event.target.value }))} />
                    </div>
                    <div className="form-group">
                      <label className="form-label">Semester</label>
                      <input className="form-control" value={counselorSendVars.semester} onChange={(event) => setCounselorSendVars((prev) => ({ ...prev, semester: event.target.value }))} />
                    </div>
                  </div>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Batch</label>
                        <input className="form-control" value={counselorSendVars.batch_name} onChange={(event) => setCounselorSendVars((prev) => ({ ...prev, batch_name: event.target.value }))} />
                      </div>
                      <div className="form-group">
                        <label className="form-label">{counselorSendEmbeddedWhatsappActive ? 'Desktop Send Flow' : 'WhatsApp Link Mode'}</label>
                      {counselorSendEmbeddedWhatsappActive ? (
                        <>
                          <div className="badge badge-info" style={{ width: 'fit-content' }}>Desktop WhatsApp Workspace</div>
                          <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', display: 'block', marginTop: 6 }}>
                            Desktop sends keep the floating student list active while opening WhatsApp Desktop.
                          </small>
                        </>
                      ) : (
                        <>
                          <div className="btn-group" style={{ justifyContent: 'flex-start' }}>
                            <button
                              type="button"
                              className={`btn btn-sm ${counselorSendVars.sendMode === 'app' ? 'btn-primary' : 'btn-outline'}`}
                              onClick={() => void openCounselorSendPage(counselorSendPage.testId, 'app')}
                            >
                              App
                            </button>
                            <button
                              type="button"
                              className={`btn btn-sm ${counselorSendVars.sendMode === 'web' ? 'btn-primary' : 'btn-outline'}`}
                              onClick={() => void openCounselorSendPage(counselorSendPage.testId, 'web')}
                              disabled={isMobileUi()}
                            >
                              Web
                            </button>
                          </div>
                          <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', display: 'block', marginTop: 6 }}>
                            {isMobileUi()
                              ? 'Mobile UI uses WhatsApp app mode only.'
                              : counselorSendVars.sendMode === 'web'
                                ? 'Web mode opens WhatsApp Web in this same tab.'
                                : 'App mode opens the WhatsApp app link directly.'}
                          </small>
                        </>
                      )}
                    </div>
                  </div>
                  <div className="form-group">
                    <label className="form-label">Message Template</label>
                    <textarea
                      className="form-control"
                      rows={8}
                      value={counselorSendVars.template}
                      onChange={(event) => setCounselorSendVars((prev) => ({ ...prev, template: event.target.value }))}
                    />
                  </div>
                  <div className="form-group" style={{ marginTop: 14 }}>
                    <label className="form-label">Subject/Metric Order for Message</label>
                    <div className="text-muted" style={{ fontSize: '.82rem', marginBottom: 8 }}>
                      Arrange subject order for message body. Pending: {counselorSendPage.rows.filter((row) => row.status !== 'Generated').length}, Generated: {counselorSendPage.rows.filter((row) => row.status === 'Generated').length}.
                    </div>
                    <div className="field-order-list">
                      {counselorFieldOrder.map((entry, index) => (
                        <div key={`${entry.type}-${entry.type === 'subject' ? entry.normalizedKey : entry.metricKey}`} className="field-order-tab">
                          <div className="field-order-tab-label">{entry.label}</div>
                          <div className="field-order-tab-actions">
                            <button type="button" className="btn btn-outline btn-sm" onClick={() => moveCounselorFieldOrder(index, -1)} disabled={index === 0}>
                              <i className="fas fa-arrow-up"></i>
                            </button>
                            <button type="button" className="btn btn-outline btn-sm" onClick={() => moveCounselorFieldOrder(index, 1)} disabled={index === counselorFieldOrder.length - 1}>
                              <i className="fas fa-arrow-down"></i>
                            </button>
                          </div>
                        </div>
                      ))}
                    </div>
                    <div className="btn-group mt-1">
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => setCounselorFieldOrder(counselorDefaultFieldOrder.map((item) => ({ ...item })))}>
                        <i className="fas fa-rotate-left"></i> Reset Default Order
                      </button>
                    </div>
                  </div>
                </div>

                <div className="table-wrapper table-scroll-lg">
                  <table className={counselorSendEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted ? 'sticky-table desktop-send-queue-table' : 'sticky-table'}>
                    <thead>
                      <tr>
                        <th>Reg No</th>
                        <th>Name</th>
                        <th>Phone</th>
                        <th>Status</th>
                        {(!counselorSendEmbeddedWhatsappActive || !desktopWhatsappWorkspaceStarted) ? <th>Action</th> : null}
                      </tr>
                    </thead>
                    <tbody>
                      {counselorSendPage.rows.length ? counselorSendPage.rows.map((row) => (
                        <tr
                          key={row.reg_no}
                          className={counselorSendEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted
                            ? `desktop-send-queue-row ${row.status === 'Generated' ? 'is-generated' : ''} ${desktopWhatsappActiveTarget?.kind === 'report' && desktopWhatsappActiveTarget.regNo === row.reg_no ? 'is-active' : ''}`
                            : ''}
                          onClick={counselorSendEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted ? (() => void handleCounselorDesktopQueuePick(row)) : undefined}
                        >
                          <td><strong>{row.reg_no}</strong></td>
                          <td>{row.student_name}</td>
                          <td>{row.parent_phone || '-'}</td>
                          <td>
                            <span className={`badge ${row.status === 'Generated' ? 'badge-success' : 'badge-warning'}`}>{row.status}</span>
                          </td>
                          {(!counselorSendEmbeddedWhatsappActive || !desktopWhatsappWorkspaceStarted) ? (
                            <td>
                              <button
                                type="button"
                                className={`btn btn-primary btn-sm ${row.status === 'Generated' ? 'send-btn-generated' : ''}`}
                                onClick={() => void (counselorSendEmbeddedWhatsappActive ? handleCounselorDesktopQueuePick(row) : handleCounselorSendSingle(row))}
                              >
                                <i className="fab fa-whatsapp"></i> Send To WhatsApp
                              </button>
                            </td>
                          ) : null}
                        </tr>
                      )) : (
                        <tr><td colSpan={counselorSendEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted ? 4 : 5} className="text-center text-muted" style={{ padding: 18 }}>No students available for this test.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>

                <div style={{ height: 48 }}></div>

                {counselorSendEmbeddedWhatsappActive ? (
                    <div className="card" id="batchSendCard">
                      <div className="card-title"><i className="fas fa-list-check"></i> Desktop Send Queue</div>
                      <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 0 }}>
                      Desktop workspace mode keeps the split send layout active. Open each student from the list and continue through the queue without leaving the workspace.
                      </p>
                    </div>
                ) : counselorSendPage.batchSendEnabled && !isMobileUi() ? (
                  <div className="card" id="batchSendCard">
                    <div className="card-title d-flex justify-between align-center">
                      <span><i className="fas fa-layer-group"></i> Batch Send Controls</span>
                      <span className={`badge ${counselorBatchRunning ? 'badge-success' : 'badge-warning'}`}>{counselorBatchRunning ? 'Running' : counselorBatchIndex > 0 ? 'Paused' : 'Inactive'}</span>
                    </div>
                    <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                      Automatically advance through pending students. <strong>Requires WhatsApp App mode.</strong> A delay of <strong>{counselorSendPage.batchSendDelaySeconds}s</strong> is applied between each send.
                    </p>
                    <div className="form-check mb-4" style={{ background: 'var(--bg-input)', padding: '12px 16px', borderRadius: 'var(--radius-sm)', border: '1px solid var(--border)' }}>
                      <input
                        type="checkbox"
                        id="batchIncludeGenerated"
                        checked={counselorIncludeGenerated}
                        onChange={(event) => {
                          stopCounselorBatchSend();
                          setCounselorIncludeGenerated(event.target.checked);
                          setCounselorBatchIndex(0);
                          counselorBatchIndexRef.current = 0;
                        }}
                      />
                      <label htmlFor="batchIncludeGenerated">Include already sent students (Resend From Beginning)</label>
                    </div>
                    <div className="d-flex align-center flex-wrap" style={{ gap: 12 }}>
                      {!counselorBatchRunning ? (
                        <button type="button" className="btn btn-success" onClick={() => startCounselorBatchSend()}>
                          <i className="fas fa-play"></i> {counselorBatchIndex > 0 ? `Resume Batch Send (${Math.max(0, counselorBatchQueueRef.current.length - counselorBatchIndex)} Remaining)` : `Start Batch Send (${counselorSendPage.rows.filter((row) => counselorIncludeGenerated || row.status !== 'Generated').length} Students)`}
                        </button>
                      ) : null}
                      {counselorBatchRunning ? (
                        <div style={{ fontSize: '.82rem', color: 'var(--text-dim)' }}>
                          Running... Current: <strong>{counselorBatchQueueRef.current[counselorBatchIndex]?.student_name || 'None'}</strong>
                        </div>
                      ) : null}
                    </div>
                    {counselorBatchLastStudent ? (
                      <div className="mt-3" style={{ paddingTop: 12, borderTop: '1px solid var(--border)' }}>
                        <div style={{ fontSize: '.75rem', textTransform: 'uppercase', letterSpacing: '0.5px', color: 'var(--text-muted)', marginBottom: 4 }}>Last Student Processed</div>
                        <div style={{ fontSize: '.88rem', fontWeight: 600 }}>{counselorBatchLastStudent}</div>
                      </div>
                    ) : null}
                    {counselorBatchRunning ? (
                      <div className="mt-2" style={{ fontSize: '.78rem', color: 'var(--warning)' }}>
                        <i className="fas fa-exclamation-triangle"></i> Please keep this tab active and do not close the WhatsApp windows.
                      </div>
                    ) : null}
                  </div>
                ) : null}
                </>
                )}
              </>
            ) : null
          ) : currentUser.role === 'counselor' && activeTab === 'notices' && counselorNoticeSendVerify ? (
            <>
              <div className="report-sticky-toolbar mb-2">
                <div className="report-toolbar-balanced">
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => setCounselorNoticeSendVerify(null)}
                  >
                    <i className="fas fa-arrow-left"></i> Back To Notices
                  </button>
                  <div className="report-toolbar-center">
                    <span className="badge badge-info">{counselorNoticeSendVerify.noticeTitle || 'Selected Notice'}</span>
                  </div>
                  <div></div>
                </div>
              </div>

              <div className="card" style={{ maxWidth: 780 }}>
                <div className="card-title"><i className="fab fa-whatsapp"></i> WhatsApp App Verification</div>
                <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                  We are checking whether the WhatsApp app is available on this device. This takes about 5 seconds.
                </p>

                <div
                  className="card"
                  style={{
                    padding: 12,
                    border: `1px solid ${
                      counselorNoticeSendVerify.tone === 'success'
                        ? 'rgba(34,197,94,.35)'
                        : counselorNoticeSendVerify.tone === 'error'
                          ? 'rgba(239,68,68,.35)'
                          : 'var(--border)'
                    }`,
                    background: 'var(--bg-input)',
                  }}
                >
                  <strong>{counselorNoticeSendVerify.title}</strong>
                  <div style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginTop: 6 }}>{counselorNoticeSendVerify.body}</div>
                </div>

                {counselorNoticeSendVerify.appFound ? (
                  <div style={{ display: 'flex', gap: 10, flexWrap: 'wrap', marginTop: 14 }}>
                    <button type="button" className="btn btn-success" onClick={() => void openCounselorNoticeSendPage(counselorNoticeSendVerify.noticeId, 'app')}>
                      <i className="fas fa-check"></i> Continue (WhatsApp App)
                    </button>
                    <button type="button" className="btn btn-outline" onClick={() => void openCounselorNoticeSendPage(counselorNoticeSendVerify.noticeId, 'web')}>
                      <i className="fas fa-globe"></i> Use WhatsApp Web
                    </button>
                  </div>
                ) : null}

                {counselorNoticeSendVerify.completed && !counselorNoticeSendVerify.appFound ? (
                  <div style={{ display: 'flex', gap: 10, flexWrap: 'wrap', marginTop: 14 }}>
                    <button type="button" className="btn btn-primary" onClick={() => installWhatsappForNoticeAndReturn()}>
                      <i className="fas fa-download"></i> Install WhatsApp App And Continue
                    </button>
                    <button type="button" className="btn btn-outline" onClick={() => void openCounselorNoticeSendPage(counselorNoticeSendVerify.noticeId, 'web')}>
                      <i className="fas fa-globe"></i> Use WhatsApp Web
                    </button>
                  </div>
                ) : null}
              </div>
            </>
          ) : currentUser.role === 'counselor' && activeTab === 'notices' && (counselorNoticeSendLoading || counselorNoticeSendPage) ? (
            counselorNoticeSendLoading ? (
              <div className="card">
                <div className="panel-placeholder">Loading send notice page...</div>
              </div>
            ) : counselorNoticeSendPage ? (
              <>
                {!embeddedWhatsappSidepaneLayoutActive ? (
                  <div className="report-sticky-toolbar mb-2">
                    <div className="report-toolbar-balanced">
                      <button
                        type="button"
                        className="btn btn-outline btn-sm"
                        onClick={() => {
                          stopCounselorNoticeBatchSend();
                          void stopDesktopWhatsappWorkspaceImmediate();
                          setCounselorNoticeSendPage(null);
                        }}
                      >
                        <i className="fas fa-arrow-left"></i> Back To Notices
                      </button>
                      <div className="report-toolbar-center">
                        <span className="badge badge-info">{counselorNoticeSendPage.notice.title_display || 'Selected Notice'}</span>
                      </div>
                      <div></div>
                    </div>
                  </div>
                ) : null}

                {counselorNoticeEmbeddedWhatsappActive ? (
                  <div
                    className={`desktop-send-workspace-layout ${embeddedWhatsappSidepaneLayoutActive ? 'is-compact' : ''}`}
                    ref={desktopNoticeWorkspaceRef}
                  >
                    <div className="desktop-send-workspace-main">
                      <div className="card mb-3">
                        <div className="card-title"><i className="fas fa-pen-to-square"></i> Message Template</div>
                        <div className="form-row">
                          <div className="form-group">
                            <label className="form-label">Notice Title</label>
                            <input
                              className="form-control"
                              defaultValue={counselorNoticeSendVars.title}
                              onChange={(event) => { counselorNoticeSendVarsRef.current = { ...counselorNoticeSendVarsRef.current, title: event.target.value }; }}
                              onBlur={() => setCounselorNoticeSendVars((prev) => ({ ...prev, title: counselorNoticeSendVarsRef.current.title }))}
                            />
                          </div>
                    <div className="form-group">
                            <label className="form-label">Send Mode</label>
                            <div className="segmented-switch send-mode-switch" data-count={2} data-mode={counselorNoticeSendVars.sendMode === 'embed' ? 'app' : counselorNoticeSendVars.sendMode}>
                              <div className="segmented-switch-thumb" aria-hidden="true"></div>
                              <button
                                type="button"
                                className={`segmented-switch-option ${counselorNoticeSendVars.sendMode === 'app' || counselorNoticeSendVars.sendMode === 'embed' ? 'active' : ''}`}
                                onClick={() => void handleCounselorNoticeSendModeChange('app')}
                              >
                                App
                              </button>
                              <button
                                type="button"
                                className={`segmented-switch-option ${counselorNoticeSendVars.sendMode === 'web' ? 'active' : ''}`}
                                onClick={() => void handleCounselorNoticeSendModeChange('web')}
                              >
                                Web
                              </button>
                            </div>
                            <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', display: 'block', marginTop: 6 }}>
                              {counselorNoticeSendVars.sendMode === 'web'
                                  ? 'Web mode keeps the normal WhatsApp Web flow.'
                                  : 'App mode opens the floating student list after you start the workflow.'}
                            </small>
                          </div>
                        </div>
                        <div className="form-group">
                          <label className="form-label">Notice Caption / Text</label>
                          <textarea
                            className="form-control"
                            rows={4}
                            defaultValue={counselorNoticeSendVars.text}
                            onChange={(event) => { counselorNoticeSendVarsRef.current = { ...counselorNoticeSendVarsRef.current, text: event.target.value }; }}
                            onBlur={() => setCounselorNoticeSendVars((prev) => ({ ...prev, text: counselorNoticeSendVarsRef.current.text }))}
                          />
                        </div>
                        <div className="form-group">
                          <label className="form-label">Message Template</label>
                          <textarea
                            className="form-control"
                            rows={7}
                            defaultValue={counselorNoticeSendVars.template}
                            onChange={(event) => {
                              setCounselorNoticeTemplateEdited(true);
                              counselorNoticeSendVarsRef.current = { ...counselorNoticeSendVarsRef.current, template: event.target.value };
                            }}
                            onBlur={() => setCounselorNoticeSendVars((prev) => ({ ...prev, template: counselorNoticeSendVarsRef.current.template }))}
                          />
                          <small style={{ color: 'var(--text-dim)', fontSize: '.76rem', display: 'block', marginTop: 6 }}>
                            This starts with the default parent message format. You can edit it locally for this send session, and optional placeholders like <code>{'{student_name}'}</code> and <code>{'{reg_no}'}</code> still work if you add them manually.
                          </small>
                        </div>
                        {(counselorNoticeSendVars.sendMode === 'app' || counselorNoticeSendVars.sendMode === 'web' || counselorNoticeSendVars.sendMode === 'embed') && !desktopWhatsappWorkspaceStarted ? (
                          <div className="desktop-send-template-footer">
                            <button
                              type="button"
                              className="btn btn-success desktop-send-start-btn"
                              disabled={desktopWhatsappWorkspaceBusy}
                              onClick={() => void startDesktopWhatsappWorkspace('notice')}
                            >
                              <i className={`fas ${desktopWhatsappWorkspaceBusy ? 'fa-spinner fa-spin' : 'fa-play'}`}></i> {desktopWhatsappWorkspaceBusy ? 'Opening...' : 'Start Workflow'}
                            </button>
                          </div>
                        ) : null}
                      </div>

                      <div className="card mb-3" id="noticeAttachmentsCard">
                        <div className="card-title"><i className="fas fa-paperclip"></i> Attachments</div>
                        {counselorNoticeSendPage.attachments.length ? (
                          <div className="table-wrapper">
                            <table>
                              <thead>
                                <tr>
                                  <th>File</th>
                                  <th>Type</th>
                                  <th>Size</th>
                                  <th>Preview</th>
                                </tr>
                              </thead>
                              <tbody>
                                {counselorNoticeSendPage.attachments.map((attachment) => (
                                  <tr key={attachment.id}>
                                    <td><strong>{attachment.original_name}</strong></td>
                                    <td>{attachment.mime_type || 'Document'}</td>
                                    <td>{`${(((attachment.file_size || 0) / 1024) || 0).toFixed(1)} KB`}</td>
                                    <td>
                                      {(() => {
                                        const previewUrl = buildNoticeAttachmentPreviewUrl(attachment);
                                        return (
                                      <a
                                        className="btn btn-outline btn-sm"
                                        href={previewUrl}
                                        target="_blank"
                                        rel="noreferrer"
                                        onClick={(event) => {
                                          if (!runtimeConfig.isDesktop) return;
                                          event.preventDefault();
                                          openExternalLink(previewUrl);
                                        }}
                                      >
                                        <i className="fas fa-eye"></i> Open
                                      </a>
                                        );
                                      })()}
                                    </td>
                                  </tr>
                                ))}
                              </tbody>
                            </table>
                          </div>
                        ) : (
                          <p className="text-muted" style={{ fontSize: '.84rem', margin: 0 }}>This notice has no attachments. Text-only sending is enabled.</p>
                        )}
                      </div>

                      {counselorNoticeDesktopWorkspaceMode ? (
                        <div className="desktop-send-lite-summary">
                          <span className="badge badge-info">{counselorNoticeRowCounts.total} students loaded</span>
                          <span className="badge badge-warning">{counselorNoticeRowCounts.pending} pending</span>
                          <span className="badge badge-success">{counselorNoticeRowCounts.generated} generated</span>
                        </div>
                      ) : (
                        <div className="table-wrapper" id="noticeSendTable">
                          <table className="sticky-table">
                            <thead>
                              <tr>
                                <th>Reg No</th>
                                <th>Name</th>
                                <th>Phone</th>
                                <th>Status</th>
                                <th>Action</th>
                              </tr>
                            </thead>
                            <tbody>
                              {counselorNoticeSendPage.rows.length ? counselorNoticeSendPage.rows.map((row) => (
                                <tr key={row.reg_no}>
                                  <td><strong>{row.reg_no}</strong></td>
                                  <td>{row.student_name}</td>
                                  <td>{row.parent_phone || '-'}</td>
                                  <td>
                                    <span className={`badge ${row.status === 'Generated' ? 'badge-success' : 'badge-warning'}`}>{row.status}</span>
                                  </td>
                                  <td>
                                    <button
                                      type="button"
                                      className={`btn btn-primary btn-sm ${row.status === 'Generated' ? 'send-btn-generated' : ''}`}
                                      onClick={() => void handleCounselorNoticeSendSingle(row)}
                                    >
                                      <i className="fab fa-whatsapp"></i> Send To WhatsApp
                                    </button>
                                  </td>
                                </tr>
                              )) : (
                                <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 18 }}>No students are assigned to your account yet.</td></tr>
                              )}
                            </tbody>
                          </table>
                        </div>
                      )}
                    </div>

                    {embeddedWhatsappSidepaneLayoutActive && counselorNoticeDesktopWorkspaceMode ? (
                    <aside className="desktop-send-workspace-pane">
                      <div className="desktop-send-sidepane-panel">
                        <div className={`desktop-send-student-list-shell ${desktopWhatsappWorkspaceExiting ? 'is-exiting' : ''}`} ref={desktopNoticeQueueShellRef}>
                          <div className="card-title"><i className="fas fa-user-group"></i> Student Send List</div>
                          {desktopWhatsappWorkspaceBusy ? (
                            <div className="desktop-send-workspace-loader">
                              <div className="spinner-ring" aria-hidden="true"></div>
                              <div className="desktop-send-workspace-loader-copy">Preparing WhatsApp workspace...</div>
                            </div>
                          ) : (
                            <div className="desktop-send-student-list">
                              {counselorNoticeSendPage.rows.length ? counselorNoticeSendPage.rows.map((row) => (
                                <div
                                  key={row.reg_no}
                                  className={`desktop-send-student-item ${row.status === 'Generated' ? 'is-generated' : ''} ${desktopWhatsappActiveTarget?.kind === 'notice' && desktopWhatsappActiveTarget.regNo === row.reg_no ? 'is-active' : ''}`}
                                >
                                  <div className="desktop-send-student-main">
                                  <div className="desktop-send-student-name">{row.student_name}</div>
                                    {desktopWhatsappActiveTarget?.kind === 'notice' && desktopWhatsappActiveTarget.regNo === row.reg_no ? null : desktopNoticeQueueState[row.reg_no] ? (
                                      <span className="desktop-send-student-active">{desktopNoticeQueueState[row.reg_no].toUpperCase()}</span>
                                    ) : null}
                                  </div>
                                  <button
                                    type="button"
                                    className={`btn btn-primary btn-sm desktop-send-student-button ${row.status === 'Generated' ? 'send-btn-generated' : ''}`}
                                    disabled={desktopWhatsappLoadingRow === row.reg_no}
                                    onClick={() => void handleCounselorNoticeDesktopQueuePick(row)}
                                  >
                                    <i className={desktopWhatsappLoadingRow === row.reg_no ? 'fas fa-spinner fa-spin' : 'fab fa-whatsapp'}></i> {desktopWhatsappLoadingRow === row.reg_no ? 'Opening...' : 'Send To WhatsApp'}
                                  </button>
                                </div>
                              )) : (
                                <div className="text-muted" style={{ fontSize: '.84rem' }}>No students are assigned to your account yet.</div>
                              )}
                            </div>
                          )}
                        </div>
                      </div>
                    </aside>
                    ) : null}
                  </div>
                ) : (
                <>
                <div className="card mb-3">
                  <div className="card-title"><i className="fas fa-pen-to-square"></i> Message Template</div>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Notice Title</label>
                        <input
                          className="form-control"
                        value={counselorNoticeSendVars.title}
                        onChange={(event) => setCounselorNoticeSendVars((prev) => ({ ...prev, title: event.target.value }))}
                      />
                    </div>
                    <div className="form-group">
                      <label className="form-label">{counselorNoticeEmbeddedWhatsappActive ? 'Desktop Send Flow' : 'WhatsApp Link Mode'}</label>
                      {counselorNoticeEmbeddedWhatsappActive ? (
                        <>
                          <div className="badge badge-info" style={{ width: 'fit-content' }}>Desktop WhatsApp Workspace</div>
                          <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', display: 'block', marginTop: 6 }}>
                            Desktop sends keep the floating student list active while opening WhatsApp Desktop.
                          </small>
                        </>
                      ) : (
                        <>
                          <div className="btn-group" style={{ justifyContent: 'flex-start' }}>
                            <button
                              type="button"
                              className={`btn btn-sm ${counselorNoticeSendVars.sendMode === 'app' ? 'btn-primary' : 'btn-outline'}`}
                              onClick={() => void openCounselorNoticeSendPage(counselorNoticeSendPage.noticeId, 'app')}
                            >
                              App
                            </button>
                            <button
                              type="button"
                              className={`btn btn-sm ${counselorNoticeSendVars.sendMode === 'web' ? 'btn-primary' : 'btn-outline'}`}
                              onClick={() => void openCounselorNoticeSendPage(counselorNoticeSendPage.noticeId, 'web')}
                              disabled={isMobileUi()}
                            >
                              Web
                            </button>
                          </div>
                          <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', display: 'block', marginTop: 6 }}>
                            {isMobileUi()
                              ? 'Mobile UI uses WhatsApp app mode only.'
                              : counselorNoticeSendVars.sendMode === 'web'
                                ? 'Web mode opens WhatsApp Web in this same tab.'
                                : 'App mode opens the WhatsApp app link directly.'}
                          </small>
                        </>
                      )}
                    </div>
                  </div>
                  <div className="form-group">
                    <label className="form-label">Notice Caption / Text</label>
                    <textarea
                      className="form-control"
                      rows={4}
                      value={counselorNoticeSendVars.text}
                      onChange={(event) => setCounselorNoticeSendVars((prev) => ({ ...prev, text: event.target.value }))}
                    />
                  </div>
                  <div className="form-group">
                    <label className="form-label">Message Template</label>
                    <textarea
                      className="form-control"
                      rows={7}
                      value={counselorNoticeSendVars.template}
                      onChange={(event) => {
                        setCounselorNoticeTemplateEdited(true);
                        setCounselorNoticeSendVars((prev) => ({ ...prev, template: event.target.value }));
                      }}
                    />
                    <small style={{ color: 'var(--text-dim)', fontSize: '.76rem', display: 'block', marginTop: 6 }}>
                      This starts with the default parent message format. You can edit it locally for this send session, and optional placeholders like <code>{'{student_name}'}</code> and <code>{'{reg_no}'}</code> still work if you add them manually.
                    </small>
                  </div>
                </div>

                <div className="card mb-3" id="noticeAttachmentsCard">
                  <div className="card-title"><i className="fas fa-paperclip"></i> Attachments</div>
                  {counselorNoticeSendPage.attachments.length ? (
                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>File</th>
                            <th>Type</th>
                            <th>Size</th>
                            <th>Preview</th>
                          </tr>
                        </thead>
                        <tbody>
                          {counselorNoticeSendPage.attachments.map((attachment) => (
                            <tr key={attachment.id}>
                              <td><strong>{attachment.original_name}</strong></td>
                              <td>{attachment.mime_type || 'Document'}</td>
                              <td>{`${(((attachment.file_size || 0) / 1024) || 0).toFixed(1)} KB`}</td>
                              <td>
                                {(() => {
                                  const previewUrl = buildNoticeAttachmentPreviewUrl(attachment);
                                  return (
                                <a
                                  className="btn btn-outline btn-sm"
                                  href={previewUrl}
                                  target="_blank"
                                  rel="noreferrer"
                                  onClick={(event) => {
                                    if (!runtimeConfig.isDesktop) return;
                                    event.preventDefault();
                                    openExternalLink(previewUrl);
                                  }}
                                >
                                  <i className="fas fa-eye"></i> Open
                                </a>
                                  );
                                })()}
                              </td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                  ) : (
                    <p className="text-muted" style={{ fontSize: '.84rem', margin: 0 }}>This notice has no attachments. Text-only sending is enabled.</p>
                  )}
                </div>

                <div className="table-wrapper" id="noticeSendTable">
                  <table className={counselorNoticeEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted ? 'desktop-send-queue-table' : ''}>
                    <thead>
                      <tr>
                        <th>Reg No</th>
                        <th>Name</th>
                        <th>Phone</th>
                        <th>Status</th>
                        {(!counselorNoticeEmbeddedWhatsappActive || !desktopWhatsappWorkspaceStarted) ? <th>Action</th> : null}
                      </tr>
                    </thead>
                    <tbody>
                      {counselorNoticeSendPage.rows.length ? counselorNoticeSendPage.rows.map((row) => (
                        <tr
                          key={row.reg_no}
                          className={counselorNoticeEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted
                            ? `desktop-send-queue-row ${row.status === 'Generated' ? 'is-generated' : ''} ${desktopWhatsappActiveTarget?.kind === 'notice' && desktopWhatsappActiveTarget.regNo === row.reg_no ? 'is-active' : ''}`
                            : ''}
                          onClick={counselorNoticeEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted ? (() => void handleCounselorNoticeDesktopQueuePick(row)) : undefined}
                        >
                          <td><strong>{row.reg_no}</strong></td>
                          <td>{row.student_name}</td>
                          <td>{row.parent_phone || '-'}</td>
                          <td>
                            <span className={`badge ${row.status === 'Generated' ? 'badge-success' : 'badge-warning'}`}>{row.status}</span>
                          </td>
                          {(!counselorNoticeEmbeddedWhatsappActive || !desktopWhatsappWorkspaceStarted) ? (
                            <td>
                              <button
                                type="button"
                                className={`btn btn-primary btn-sm ${row.status === 'Generated' ? 'send-btn-generated' : ''}`}
                                onClick={() => void (counselorNoticeEmbeddedWhatsappActive ? handleCounselorNoticeDesktopQueuePick(row) : handleCounselorNoticeSendSingle(row))}
                              >
                                <i className="fab fa-whatsapp"></i> Send To WhatsApp
                              </button>
                            </td>
                          ) : null}
                        </tr>
                      )) : (
                        <tr><td colSpan={counselorNoticeEmbeddedWhatsappActive && desktopWhatsappWorkspaceStarted ? 4 : 5} className="text-center text-muted" style={{ padding: 18 }}>No students are assigned to your account yet.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>

                <div style={{ height: 48 }}></div>

                {counselorNoticeEmbeddedWhatsappActive ? (
                  <div className="card" id="noticeBatchSendCard">
                    <div className="card-title"><i className="fas fa-list-check"></i> Desktop Send Queue</div>
                    <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 0 }}>
                      Desktop workspace mode keeps the split send layout active. Open each notice from the list and continue through the queue without leaving the workspace.
                    </p>
                  </div>
                ) : counselorNoticeSendPage.batchSendEnabled && !isMobileUi() ? (
                  <div className="card" id="noticeBatchSendCard">
                    <div className="card-title d-flex justify-between align-center">
                      <span><i className="fas fa-layer-group"></i> Batch Send Controls</span>
                      <span className={`badge ${counselorNoticeBatchRunning ? 'badge-success' : 'badge-warning'}`}>{counselorNoticeBatchRunning ? 'Running' : counselorNoticeBatchIndex > 0 ? 'Paused' : 'Inactive'}</span>
                    </div>
                    <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                      Automatically advance through pending students. <strong>Requires WhatsApp App mode.</strong> A delay of <strong>{counselorNoticeSendPage.batchSendDelaySeconds}s</strong> is applied between each send.
                    </p>
                    <div className="form-check mb-4" style={{ background: 'var(--bg-input)', padding: '12px 16px', borderRadius: 'var(--radius-sm)', border: '1px solid var(--border)' }}>
                      <input
                        type="checkbox"
                        id="noticeBatchIncludeGenerated"
                        checked={counselorNoticeIncludeGenerated}
                        onChange={(event) => {
                          stopCounselorNoticeBatchSend();
                          setCounselorNoticeIncludeGenerated(event.target.checked);
                          setCounselorNoticeBatchIndex(0);
                          counselorNoticeBatchIndexRef.current = 0;
                        }}
                      />
                      <label htmlFor="noticeBatchIncludeGenerated">Include already sent students (Resend From Beginning)</label>
                    </div>
                    <div className="d-flex align-center flex-wrap" style={{ gap: 12 }}>
                      {!counselorNoticeBatchRunning ? (
                        <button type="button" className="btn btn-success" onClick={() => startCounselorNoticeBatchSend()}>
                          <i className="fas fa-play"></i> {counselorNoticeBatchIndex > 0 ? `Resume Batch Send (${Math.max(0, counselorNoticeBatchQueueRef.current.length - counselorNoticeBatchIndex)} Remaining)` : `Start Batch Send (${counselorNoticeSendPage.rows.filter((row) => counselorNoticeIncludeGenerated || row.status !== 'Generated').length} Students)`}
                        </button>
                      ) : null}
                      {counselorNoticeBatchRunning ? (
                        <div style={{ fontSize: '.82rem', color: 'var(--text-dim)' }}>
                          Running... Current: <strong>{counselorNoticeBatchQueueRef.current[counselorNoticeBatchIndex]?.student_name || 'None'}</strong>
                        </div>
                      ) : null}
                    </div>
                    {counselorNoticeBatchLastStudent ? (
                      <div className="mt-3" style={{ paddingTop: 12, borderTop: '1px solid var(--border)' }}>
                        <div style={{ fontSize: '.75rem', textTransform: 'uppercase', letterSpacing: '0.5px', color: 'var(--text-muted)', marginBottom: 4 }}>Last Student Processed</div>
                        <div style={{ fontSize: '.88rem', fontWeight: 600 }}>{counselorNoticeBatchLastStudent}</div>
                      </div>
                    ) : null}
                    {counselorNoticeBatchRunning ? (
                      <div className="mt-2" style={{ fontSize: '.78rem', color: 'var(--warning)' }}>
                        <i className="fas fa-exclamation-triangle"></i> Please keep this tab active and do not close the WhatsApp windows.
                      </div>
                    ) : null}
                  </div>
                ) : null}
                </>
                )}
              </>
            ) : null
          ) : currentUser.role === 'counselor' && activeTab === 'recent-tests' ? (
            <>
              <div className="metrics-grid mb-3">
                <div className="metric-card">
                  <div className="metric-label">My Students</div>
                  <div className="metric-value">{counselorOverview?.studentCount ?? bootstrap?.metrics.studentCount ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-user-graduate"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Visible Tests</div>
                  <div className="metric-value">{counselorOverview?.testCount ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-clipboard-check"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Messages Sent</div>
                  <div className="metric-value">{counselorOverview?.messageStats.total ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-paper-plane"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">This Week</div>
                  <div className="metric-value">{counselorOverview?.messageStats.week ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-calendar-week"></i></div>
                </div>
              </div>

              <h3 className="section-title"><i className="fas fa-gauge"></i> Dashboard</h3>

              <div className="counselor-insights-stack mb-3">
                <div className="card counselor-insight-card" id="topPerformingStudentsCard" style={{ padding: 14 }}>
                  <div className="card-title"><i className="fas fa-trophy"></i> Top Performing Students</div>
                  {counselorTopPerformingStudents.length ? (
                    <div className="student-performance-list">
                      {counselorTopPerformingStudents.map((student) => (
                        <div className="student-performance-item" key={`top-${student.reg_no}`}>
                          <div className="student-performance-main">
                            <span className="student-performance-name">{student.name}</span>
                            <span className="student-performance-gpa">GPA {Number(student.gpa || 0).toFixed(2)}</span>
                          </div>
                          <div className="student-performance-submarks">
                            {student.subject_marks.length ? student.subject_marks.map((subject) => (
                              <span className="mark-chip" key={`top-${student.reg_no}-${subject.subject}`}>{subject.subject}: {subject.marks}</span>
                            )) : (
                              <span className="text-muted" style={{ fontSize: '.8rem' }}>No subject marks available.</span>
                            )}
                          </div>
                        </div>
                      ))}
                    </div>
                  ) : (
                    <p className="text-muted" style={{ fontSize: '.84rem', margin: 0 }}>No ranking data available yet. Upload marks to generate GPA rankings.</p>
                  )}
                </div>

                <div className="card counselor-insight-card" id="studentsNeedImprovementCard" style={{ padding: 14 }}>
                  <div className="card-title"><i className="fas fa-chart-line"></i> Students Who Need Improvements</div>
                  {counselorStudentsNeedImprovement.length ? (
                    <div className="student-performance-list">
                      {counselorStudentsNeedImprovement.map((student) => (
                        <div className="student-performance-item" key={`need-${student.reg_no}`}>
                          <div className="student-performance-main">
                            <span className="student-performance-name">{student.name}</span>
                            <span className="student-performance-gpa">GPA {Number(student.gpa || 0).toFixed(2)}</span>
                          </div>
                          <div className="student-performance-submarks">
                            {student.subject_marks.length ? student.subject_marks.map((subject) => (
                              <span className="mark-chip" key={`need-${student.reg_no}-${subject.subject}`}>{subject.subject}: {subject.marks}</span>
                            )) : (
                              <span className="text-muted" style={{ fontSize: '.8rem' }}>No subject marks available.</span>
                            )}
                            {typeof student.failed_subjects === 'number' ? (
                              <span className="mark-chip" key={`need-${student.reg_no}-failed`}>No. of subjects failed: {student.failed_subjects}</span>
                            ) : null}
                          </div>
                        </div>
                      ))}
                    </div>
                  ) : (
                    <p className="text-muted" style={{ fontSize: '.84rem', margin: 0 }}>No ranking data available yet. Upload marks to generate GPA rankings.</p>
                  )}
                </div>
              </div>

              <h3 className="section-title" id="recentTestsSectionTitle"><i className="fas fa-clipboard-list"></i> Dashboard - Recent Tests</h3>
              <div className="table-wrapper mb-3">
                <table>
                  <thead>
                    <tr>
                      <th>Test Name</th>
                      <th>Year</th>
                      <th>Batch</th>
                      <th>Sem</th>
                      <th>Students</th>
                      <th>Status</th>
                      <th>Actions</th>
                    </tr>
                  </thead>
                  <tbody>
                    {counselorOverviewLoading ? (
                      <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 20 }}>Loading dashboard...</td></tr>
                    ) : counselorDashboardRecentTests.length ? counselorDashboardRecentTests.map((test) => (
                      <tr key={test.id}>
                        <td><strong>{test.test_name}</strong></td>
                        <td>{formatYearLevel(test.year_level || (currentUser.year_level || 1))}</td>
                        <td>{test.batch_name || '-'}</td>
                        <td>{test.semester || '-'}</td>
                        <td>{test.student_count || 0}</td>
                        <td>
                          {test.is_blocked ? (
                            <span className="badge badge-danger">Blocked By Admin</span>
                          ) : (test.generated_count || 0) > 0 ? (
                            <span className="badge badge-success">Uploaded: {test.generated_count}</span>
                          ) : (
                            <span className="badge badge-warning">Upload Pending</span>
                          )}
                        </td>
                        <td>
                          <div className="btn-group">
                            <button type="button" className="btn btn-outline btn-sm" onClick={() => void loadTestDetail(test.id)}>
                              <i className="fas fa-eye"></i> View/Edit
                            </button>
                            <button type="button" className="btn btn-primary btn-sm" disabled={sendResultOpeningId === test.id} onClick={() => startCounselorSendFlow(test.id, test.test_name)}>
                              <i className={`fas ${sendResultOpeningId === test.id ? 'fa-spinner fa-spin' : 'fa-paper-plane'}`}></i> {sendResultOpeningId === test.id ? 'Opening...' : 'Send Results'}
                            </button>
                          </div>
                        </td>
                      </tr>
                    )) : (
                      <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 20 }}>No recent tests available yet.</td></tr>
                    )}
                  </tbody>
                </table>
              </div>

              <div className="card mt-3" id="dashboardPendingNoticesCard">
                <div className="card-title"><i className="fas fa-bullhorn"></i> Pending Notices</div>
                {counselorDashboardPendingNotices.length ? (
                  <div className="table-wrapper table-scroll-lg">
                    <table className="sticky-table">
                      <thead>
                        <tr>
                          <th>Notice</th>
                          <th>Created</th>
                          <th>Attachments</th>
                          <th>Progress</th>
                          <th>Action</th>
                        </tr>
                      </thead>
                      <tbody>
                        {counselorDashboardPendingNotices.map((notice) => (
                          <tr key={notice.id}>
                            <td>
                              <strong>{notice.title_display}</strong><br />
                              <span className="text-muted" style={{ fontSize: '.78rem' }}>{notice.message_preview || 'Attachment-only notice'}</span>
                            </td>
                            <td>{notice.created_day || '-'}</td>
                            <td>{notice.attachment_count || 0}</td>
                            <td>
                              <span className="badge badge-warning">{notice.sent_students || 0}/{notice.student_count || notice.total_students || 0} sent</span>
                            </td>
                            <td>
                              <button type="button" className="btn btn-primary btn-sm" disabled={sendNoticeOpeningId === notice.id} onClick={() => startCounselorNoticeSendFlow(notice)}>
                                <i className={`fas ${sendNoticeOpeningId === notice.id ? 'fa-spinner fa-spin' : 'fa-paper-plane'}`}></i> {sendNoticeOpeningId === notice.id ? 'Opening...' : 'Send Notice'}
                              </button>
                            </td>
                          </tr>
                        ))}
                      </tbody>
                    </table>
                  </div>
                ) : (
                  <p className="text-muted" style={{ fontSize: '.84rem', margin: 0 }}>No pending notices are waiting in your queue right now.</p>
                )}
              </div>

            </>
          ) : ['admin', 'principal', 'hod'].includes(currentUser.role) && activeTab === 'dashboard' ? (
            <Suspense fallback={<div className="card"><div className="panel-placeholder">Loading dashboard workspace...</div></div>}>
              <DashboardTab
                currentUser={currentUser}
                dashboardLoading={dashboardLoading}
                dashboardData={dashboardData}
                formatDateTime={formatDateTime}
                formatYearLevel={formatYearLevel}
                onRefreshDashboard={() => void loadDashboardOverview()}
                onCopyActivityDefaulters={() => void handleCopyActivityDefaulters('scope')}
                onCopyDashboardNoticeDefaulters={() => void handleCopyDashboardNoticeDefaulters()}
              />
            </Suspense>
          ) : activeTab === 'notices' ? (
            <>
              <h3 className="section-title"><i className="fas fa-bullhorn"></i> Notices</h3>

              {currentUser.role !== 'counselor' ? (
                <div className="card mb-3" id="noticeComposerCard" ref={noticeComposerRef}>
                  <div className="card-title">
                    <i className="fas fa-pen-to-square"></i> {noticeForm.notice_id ? 'Edit Notice' : 'Create Notice'}
                  </div>
                  <form onSubmit={(event) => void handleSaveNotice(event)}>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Notice Title (Optional)</label>
                        <input
                          type="text"
                          className="form-control"
                          value={noticeForm.notice_title}
                          placeholder="Semester fee reminder"
                          onChange={(event) => setNoticeForm((prev) => ({ ...prev, notice_title: event.target.value }))}
                        />
                      </div>
                      <div className="form-group">
                        <label className="form-label">Attachments</label>
                        <div className="file-input-wrapper">
                          <i className="fas fa-paperclip"></i>
                          <div className="file-text">Upload images, PDFs, videos or documents</div>
                          <div className="file-name" style={{ display: noticeForm.files.length ? 'block' : 'none' }}>
                            {noticeForm.files.length ? `${noticeForm.files.length} file${noticeForm.files.length === 1 ? '' : 's'} selected` : ''}
                          </div>
                          <input
                            key={noticeFileInputKey}
                            type="file"
                            multiple
                            onChange={(event) => handleNoticeFilesSelected(event.target.files)}
                          />
                        </div>
                        {noticeForm.files.length ? (
                          <div className="scope-grid" style={{ marginTop: 10 }}>
                            {noticeForm.files.map((file, index) => (
                              <div key={`${file.name}:${file.size}:${file.lastModified}`} className="scope-chip">
                                <span>{file.name}</span>
                                <button type="button" className="btn btn-outline btn-sm" onClick={() => handleRemovePendingNoticeFile(index)}>
                                  <i className="fas fa-xmark"></i>
                                </button>
                              </div>
                            ))}
                            <button
                              type="button"
                              className="btn btn-outline btn-sm"
                              onClick={() => {
                                setNoticeForm((prev) => ({ ...prev, files: [] }));
                                setNoticeFileInputKey((prev) => prev + 1);
                              }}
                            >
                              <i className="fas fa-trash"></i> Clear New Files
                            </button>
                          </div>
                        ) : null}
                      </div>
                    </div>

                    <div className="form-group">
                      <label className="form-label">Caption / Message Text</label>
                      <textarea
                        className="form-control"
                        rows={5}
                        placeholder="Enter the notice text or leave blank for attachment-only notices."
                        value={noticeForm.notice_message_text}
                        onChange={(event) => setNoticeForm((prev) => ({ ...prev, notice_message_text: event.target.value }))}
                      />
                    </div>

                    {activeNoticeEdit?.attachments?.length ? (
                      <div className="card mb-2" style={{ padding: 12, background: 'rgba(59,130,246,.06)', border: '1px solid rgba(59,130,246,.2)' }}>
                        <div className="card-title" style={{ fontSize: '.86rem', marginBottom: 10 }}><i className="fas fa-link"></i> Existing Attachments</div>
                        <div style={{ display: 'flex', flexWrap: 'wrap', gap: 10 }}>
                          {activeNoticeEdit.attachments.map((attachment) => (
                            <label key={attachment.id} className="scope-chip" style={{ maxWidth: '100%', alignItems: 'flex-start' }}>
                              <input
                                type="checkbox"
                                checked={noticeForm.remove_attachment_ids.includes(attachment.id)}
                                onChange={(event) =>
                                  setNoticeForm((prev) => ({
                                    ...prev,
                                    remove_attachment_ids: event.target.checked
                                      ? [...prev.remove_attachment_ids, attachment.id]
                                      : prev.remove_attachment_ids.filter((id) => id !== attachment.id),
                                  }))
                                }
                              />
                              <span style={{ display: 'flex', flexDirection: 'column', gap: 2 }}>
                                <strong style={{ fontSize: '.78rem' }}>Remove {attachment.original_name}</strong>
                                <a href={buildNoticeAttachmentPreviewUrl(attachment)} target="_blank" rel="noreferrer" style={{ fontSize: '.75rem' }}>Preview current file</a>
                              </span>
                            </label>
                          ))}
                        </div>
                      </div>
                    ) : null}

                    <div className="form-check" style={{ marginBottom: 12 }}>
                      <input
                        type="checkbox"
                        id="noticeSendToAll"
                        checked={noticeForm.notice_send_to_all}
                        onChange={(event) => setNoticeForm((prev) => ({ ...prev, notice_send_to_all: event.target.checked }))}
                      />
                      <label htmlFor="noticeSendToAll">Send to all available departments and years</label>
                    </div>

                    <div className="card mb-2" style={{ padding: 12, background: 'rgba(59,130,246,.08)', border: '1px solid rgba(59,130,246,.28)' }}>
                      <div className="card-title" style={{ fontSize: '.86rem', marginBottom: 10 }}><i className="fas fa-layer-group"></i> Allocate Department / Year Scopes</div>
                      <div className="scope-grid">
                        {(noticesData?.departments || []).map((department) => (
                          <div key={department.code} className="scope-item">
                            <div className="scope-item-title">{department.code}</div>
                            <div className="scope-year-list">
                              {(noticesData?.availableYears || []).map((year) => {
                                const value = `${department.code}::${year}`;
                                return (
                                  <label key={value} className="scope-chip">
                                    <input
                                      type="checkbox"
                                      checked={noticeForm.scope_pairs.includes(value)}
                                      disabled={noticeForm.notice_send_to_all}
                                      onChange={(event) =>
                                        setNoticeForm((prev) => ({
                                          ...prev,
                                          scope_pairs: event.target.checked
                                            ? [...prev.scope_pairs, value]
                                            : prev.scope_pairs.filter((item) => item !== value),
                                        }))
                                      }
                                    />
                                    <span>Y{year}</span>
                                  </label>
                                );
                              })}
                            </div>
                          </div>
                        ))}
                      </div>
                      <small style={{ fontSize: '.74rem', color: 'var(--text-dim)' }}>Choose one or more department-year scopes for this notice.</small>
                    </div>

                    <div className="btn-group" style={{ marginTop: 12 }}>
                      <button type="submit" className="btn btn-primary" disabled={savingNotice}>
                        <i className={`fas ${savingNotice ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> {noticeForm.notice_id ? 'Update Notice' : 'Create Notice'}
                      </button>
                      {noticeForm.notice_id ? (
                        <button type="button" className="btn btn-outline" onClick={() => applyNoticeEditState(null)}>
                          <i className="fas fa-xmark"></i> Cancel Edit
                        </button>
                      ) : null}
                    </div>
                  </form>
                </div>
              ) : null}

              {currentUser.role === 'counselor' ? (
                <div className="card mb-3">
                  <form onSubmit={(event) => void handleApplyNoticeFilters(event)} className="form-row" style={{ alignItems: 'end' }}>
                  {currentUser.role !== 'counselor' ? (
                    <>
                      <div className="form-group">
                        <label className="form-label">Department</label>
                        <select className="form-control" value={noticeFilters.department} onChange={(event) => setNoticeFilters((prev) => ({ ...prev, department: event.target.value }))}>
                          <option value="">All Departments</option>
                          {(noticesData?.departments || []).map((department) => (
                            <option key={department.code} value={department.code}>{department.code}</option>
                          ))}
                        </select>
                      </div>
                      <div className="form-group">
                        <label className="form-label">Year</label>
                        <select className="form-control" value={noticeFilters.year} onChange={(event) => setNoticeFilters((prev) => ({ ...prev, year: event.target.value }))}>
                          <option value="">All Years</option>
                          {(noticesData?.availableYears || []).map((year) => (
                            <option key={year} value={year}>{formatYearLevel(year)}</option>
                          ))}
                        </select>
                      </div>
                    </>
                  ) : null}
                  <div className="form-group">
                    <label className="form-label">Status</label>
                    <select className="form-control" value={noticeFilters.status} onChange={(event) => setNoticeFilters((prev) => ({ ...prev, status: event.target.value }))}>
                      <option value="">All {currentUser.role === 'counselor' ? 'Notices' : 'Status'}</option>
                      <option value="pending">Pending</option>
                      <option value="completed">Completed</option>
                    </select>
                  </div>
                  <div className="form-group">
                    <label className="form-label">From Date</label>
                    <SmartDateInput value={noticeFilters.date_from} onChange={(nextValue) => setNoticeFilters((prev) => ({ ...prev, date_from: nextValue }))} />
                  </div>
                  <div className="form-group">
                    <label className="form-label">To Date</label>
                    <SmartDateInput value={noticeFilters.date_to} onChange={(nextValue) => setNoticeFilters((prev) => ({ ...prev, date_to: nextValue }))} />
                  </div>
                  <div className="btn-group" style={{ marginBottom: 2 }}>
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => {
                        setNoticeFilters({ department: '', year: '', status: '', date_from: '', date_to: '' });
                      }}
                    >
                      <i className="fas fa-rotate-left"></i> Reset
                    </button>
                  </div>
                  </form>
                </div>
              ) : null}

              {currentUser.role === 'counselor' ? (
                <div className="card" id="noticeRecordsCard">
                <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12, marginBottom: 14 }}>
                  <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-list"></i> Notice Records</div>
                </div>
                <div className="d-flex align-center flex-wrap" style={{ gap: 10, marginBottom: 12 }}>
                  <div style={{ flex: '1 1 320px', minWidth: 260 }}>
                    <input
                      className="form-control"
                      style={{ width: '100%' }}
                      autoComplete="off"
                      data-lpignore="true"
                      data-1p-ignore="true"
                      value={noticeRecordSearch}
                      onChange={(event) => setNoticeRecordSearch(event.target.value)}
                      placeholder="Search notice title, creator or scope"
                    />
                  </div>
                  <div className="btn-group">
                    <button type="button" className="btn btn-outline btn-sm" onClick={() => setNoticeRecordSortOpen((prev) => !prev)}>
                      <i className="fas fa-arrow-down-wide-short"></i> Sort
                    </button>
                  </div>
                </div>
                {noticeRecordSortOpen ? (
                  <div className="filter-tray" style={{ marginBottom: 14 }}>
                    <select className="form-control" value={noticeRecordSort} onChange={(event) => setNoticeRecordSort(event.target.value)} style={{ maxWidth: 220 }}>
                      <option value="latest">Latest First</option>
                      <option value="progress_desc">Highest Progress</option>
                      <option value="attachments_desc">Most Attachments</option>
                      <option value="title_asc">Title A-Z</option>
                      <option value="title_desc">Title Z-A</option>
                    </select>
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => {
                        setNoticeRecordSearch('');
                        setNoticeRecordSort('latest');
                      }}
                    >
                      <i className="fas fa-rotate-left"></i> Reset
                    </button>
                  </div>
                ) : null}
                <div className="inline-muted" style={{ marginBottom: 12 }}>
                  Showing {visibleNoticeRecords.length} notice record{visibleNoticeRecords.length === 1 ? '' : 's'}
                </div>
                <div className="table-wrapper table-scroll-lg">
                  <table className="sticky-table">
                    <thead>
                      <tr>
                        <th>Notice</th>
                        {currentUser.role !== 'counselor' ? <th>Scopes</th> : null}
                        <th>Created</th>
                        <th>Attachments</th>
                        <th>Status</th>
                        <th>Progress</th>
                        <th>Actions</th>
                      </tr>
                    </thead>
                    <tbody>
                      {noticesLoading ? (
                        <tr><td colSpan={currentUser.role !== 'counselor' ? 7 : 6} className="text-center text-muted" style={{ padding: 24 }}>Loading notices...</td></tr>
                      ) : visibleNoticeRecords.length ? visibleNoticeRecords.map((notice) => (
                        <tr key={notice.id}>
                          <td>
                            <strong>{notice.title_display}</strong><br />
                            <span style={{ fontSize: '.76rem', color: 'var(--text-dim)' }}>{notice.message_preview || 'Attachment-only notice'}</span>
                            {currentUser.role !== 'counselor' ? (
                              <>
                                <br />
                                <span style={{ fontSize: '.74rem', color: 'var(--text-muted)' }}>By {notice.created_by_name || notice.created_by || 'Unknown'}</span>
                              </>
                            ) : null}
                          </td>
                          {currentUser.role !== 'counselor' ? (
                            <td>
                              {(notice.scope_labels || []).slice(0, 3).map((label) => (
                                <span key={label} className="badge badge-info" style={{ marginRight: 6 }}>{label}</span>
                              ))}
                              {(notice.scope_labels || []).length > 3 ? <span className="badge badge-muted">+{notice.scope_labels.length - 3} more</span> : null}
                            </td>
                          ) : null}
                          <td>{notice.created_day || '-'}</td>
                          <td>{notice.attachment_count || 0}</td>
                          <td>
                            <span className={`badge ${notice.completion_status === 'completed' ? 'badge-success' : 'badge-warning'}`}>
                              {notice.completion_status === 'completed' ? 'Completed' : 'Pending'}
                            </span>
                          </td>
                          <td>
                            {currentUser.role === 'counselor' ? (
                              `${notice.sent_students || 0}/${notice.student_count || notice.total_students || 0}`
                            ) : (
                              <>
                                <div style={{ fontSize: '.8rem' }}>{notice.completed_counselors || 0}/{notice.total_counselors || 0} counselors</div>
                                <div style={{ fontSize: '.76rem', color: 'var(--text-dim)' }}>{notice.sent_students || 0}/{notice.total_students || 0} students</div>
                              </>
                            )}
                          </td>
                          <td>
                            <div className="btn-group">
                              {currentUser.role === 'counselor' ? (
                                <button type="button" className="btn btn-primary btn-sm" disabled={sendNoticeOpeningId === notice.id} onClick={() => startCounselorNoticeSendFlow(notice)}>
                                  <i className={`fas ${sendNoticeOpeningId === notice.id ? 'fa-spinner fa-spin' : 'fa-paper-plane'}`}></i> {sendNoticeOpeningId === notice.id ? 'Opening...' : 'Send Notice'}
                                </button>
                              ) : notice.can_manage_fully ? (
                                <>
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleEditNotice(notice.id)}>
                                    <i className="fas fa-pen"></i> Edit
                                  </button>
                                  <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteNoticeAction(notice)}>
                                    <i className="fas fa-trash"></i> Delete
                                  </button>
                                </>
                              ) : (
                                <span className="badge badge-info">Scoped View</span>
                              )}
                            </div>
                          </td>
                        </tr>
                      )) : (
                        <tr><td colSpan={currentUser.role !== 'counselor' ? 7 : 6} className="text-center text-muted" style={{ padding: 24 }}>No notices found for the selected filters.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>
                </div>
              ) : null}

              {currentUser.role !== 'counselor' ? (
                <div className="card mt-3" id="noticeCompletionCard">
                  <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                    <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-list-check"></i> Notice Completion List</div>
                  </div>
                  <div className="d-flex align-center flex-wrap" style={{ gap: 10, marginBottom: 12 }}>
                    <div style={{ flex: '1 1 340px', minWidth: 260 }}>
                    <input
                      className="form-control"
                      autoComplete="off"
                      data-lpignore="true"
                      data-1p-ignore="true"
                      value={noticeCompletionSearch}
                      onChange={(event) => setNoticeCompletionSearch(event.target.value)}
                      placeholder="Type counselor name, email, department or notice title"
                    />
                    </div>
                    <div className="btn-group">
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => setNoticeCompletionSortOpen((prev) => !prev)}>
                        <i className="fas fa-arrow-down-wide-short"></i> Sort
                      </button>
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleCopyNoticeDefaulters()}>
                        <i className="fas fa-copy"></i> Copy Defaulters
                      </button>
                    </div>
                  </div>
                  {noticeCompletionSortOpen ? (
                    <div className="filter-tray" style={{ marginBottom: 14 }}>
                      <select className="form-control" value={noticeCompletionDepartment} onChange={(event) => setNoticeCompletionDepartment(event.target.value)} style={{ maxWidth: 180 }}>
                        <option value="">All Departments</option>
                        {(noticesData?.departments || []).map((department) => (
                          <option key={`completion-department:${department.code}`} value={department.code}>{department.code}</option>
                        ))}
                      </select>
                      <select className="form-control" value={noticeCompletionYear} onChange={(event) => setNoticeCompletionYear(event.target.value)} style={{ maxWidth: 160 }}>
                        <option value="">All Years</option>
                        {(noticesData?.availableYears || []).map((year) => (
                          <option key={`completion-year:${year}`} value={String(year)}>{formatYearLevel(year)}</option>
                        ))}
                      </select>
                      <select className="form-control" value={noticeCompletionSort} onChange={(event) => setNoticeCompletionSort(event.target.value)} style={{ maxWidth: 220 }}>
                        <option value="pending_desc">Most Pending First</option>
                        <option value="pending_asc">Least Pending First</option>
                        <option value="completion_desc">Highest Completion</option>
                        <option value="completion_asc">Lowest Completion</option>
                        <option value="department_asc">Department / Year</option>
                        <option value="name_asc">Counselor A-Z</option>
                        <option value="name_desc">Counselor Z-A</option>
                      </select>
                      <button
                        type="button"
                        className="btn btn-outline btn-sm"
                        onClick={() => {
                          setNoticeCompletionSearch('');
                          setNoticeCompletionDepartment('');
                          setNoticeCompletionYear('');
                          setNoticeCompletionSort('pending_desc');
                        }}
                      >
                        <i className="fas fa-rotate-left"></i> Reset
                      </button>
                    </div>
                  ) : null}
                  <div className="inline-muted" style={{ marginBottom: 12 }}>
                    Showing {noticeCompletionRows.length} counselor row{noticeCompletionRows.length === 1 ? '' : 's'}
                  </div>
                  <div className="table-wrapper table-scroll-lg">
                    <table className="sticky-table">
                      <thead>
                        <tr>
                          <th>Counselor</th>
                          <th>Department</th>
                          <th>Year</th>
                          <th>Pending Notices</th>
                          <th>Completion</th>
                          <th>Action</th>
                        </tr>
                      </thead>
                      <tbody>
                        {noticeCompletionRows.length ? noticeCompletionRows.map((row) => (
                          <tr key={row.email}>
                            <td><strong>{row.name}</strong><br /><span className="inline-muted">{row.email}</span></td>
                            <td>{row.department || '-'}</td>
                            <td>{formatYearLevel(row.year_level || 1)}</td>
                            <td><span className={`badge ${row.pending_notice_count ? 'badge-warning' : 'badge-success'}`}>{row.pending_notice_count || 0}</span></td>
                            <td>
                              <div style={{ fontSize: '.82rem' }}>{row.completed_notice_count || 0}/{row.total_notice_count || 0} completed</div>
                              <div style={{ fontSize: '.76rem', color: 'var(--text-dim)' }}>{row.completion_pct || 0}%</div>
                            </td>
                            <td>
                              <button type="button" className="btn btn-outline btn-sm" onClick={() => setSelectedNoticeCompletion(row)}>
                                <i className="fas fa-eye"></i> View
                              </button>
                            </td>
                          </tr>
                        )) : (
                          <tr><td colSpan={6} className="text-center text-muted" style={{ padding: 24 }}>No counselor notice completion rows match the current search and sort filters.</td></tr>
                        )}
                      </tbody>
                    </table>
                  </div>
                </div>
              ) : null}

              {currentUser.role !== 'counselor' ? (
                <>
                  <div className="card mt-3" id="noticeRecordsCard">
                    <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                      <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-list"></i> Notice Records</div>
                    </div>
                    <div className="d-flex align-center flex-wrap" style={{ gap: 10, marginBottom: 12 }}>
                      <div style={{ flex: '1 1 340px', minWidth: 260 }}>
                        <input
                          className="form-control"
                          style={{ width: '100%' }}
                          autoComplete="off"
                          data-lpignore="true"
                          data-1p-ignore="true"
                          value={noticeRecordSearch}
                          onChange={(event) => setNoticeRecordSearch(event.target.value)}
                          placeholder="Search notice title, creator or scope"
                        />
                      </div>
                      <div className="btn-group">
                        <button type="button" className="btn btn-outline btn-sm" onClick={() => setNoticeRecordSortOpen((prev) => !prev)}>
                          <i className="fas fa-arrow-down-wide-short"></i> Sort
                        </button>
                      </div>
                    </div>
                    {noticeRecordSortOpen ? (
                    <div className="filter-tray" style={{ marginBottom: 14 }}>
                      <select className="form-control" value={noticeRecordSort} onChange={(event) => setNoticeRecordSort(event.target.value)} style={{ maxWidth: 220 }}>
                        <option value="latest">Latest First</option>
                        <option value="progress_desc">Highest Progress</option>
                        <option value="attachments_desc">Most Attachments</option>
                        <option value="title_asc">Title A-Z</option>
                        <option value="title_desc">Title Z-A</option>
                      </select>
                      <select className="form-control" value={noticeFilters.department} onChange={(event) => setNoticeFilters((prev) => ({ ...prev, department: event.target.value }))} style={{ maxWidth: 180 }}>
                        <option value="">All Departments</option>
                        {(noticesData?.departments || []).map((department) => (
                          <option key={department.code} value={department.code}>{department.code}</option>
                        ))}
                      </select>
                      <select className="form-control" value={noticeFilters.year} onChange={(event) => setNoticeFilters((prev) => ({ ...prev, year: event.target.value }))} style={{ maxWidth: 160 }}>
                        <option value="">All Years</option>
                        {(noticesData?.availableYears || []).map((year) => (
                          <option key={year} value={year}>{formatYearLevel(year)}</option>
                        ))}
                      </select>
                      <select className="form-control" value={noticeFilters.status} onChange={(event) => setNoticeFilters((prev) => ({ ...prev, status: event.target.value }))} style={{ maxWidth: 170 }}>
                        <option value="">All Status</option>
                        <option value="pending">Pending</option>
                        <option value="completed">Completed</option>
                      </select>
                      <SmartDateInput value={noticeFilters.date_from} onChange={(nextValue) => setNoticeFilters((prev) => ({ ...prev, date_from: nextValue }))} placeholder="09 Jun 2026" />
                      <SmartDateInput value={noticeFilters.date_to} onChange={(nextValue) => setNoticeFilters((prev) => ({ ...prev, date_to: nextValue }))} placeholder="20 Jun 2026" />
                      <button
                        type="button"
                        className="btn btn-outline btn-sm"
                        onClick={() => {
                          setNoticeRecordSearch('');
                          setNoticeRecordSort('latest');
                          setNoticeFilters({ department: '', year: '', status: '', date_from: '', date_to: '' });
                        }}
                      >
                        <i className="fas fa-rotate-left"></i> Reset
                      </button>
                    </div>
                    ) : null}
                    <div className="inline-muted" style={{ marginBottom: 12 }}>
                      Showing {visibleNoticeRecords.length} notice record{visibleNoticeRecords.length === 1 ? '' : 's'}
                    </div>
                    <div className="table-wrapper table-scroll-lg">
                      <table className="sticky-table">
                        <thead>
                          <tr>
                            <th>Notice</th>
                            <th>Scopes</th>
                            <th>Created</th>
                            <th>Attachments</th>
                            <th>Status</th>
                            <th>Progress</th>
                            <th>Actions</th>
                          </tr>
                        </thead>
                        <tbody>
                          {noticesLoading ? (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading notices...</td></tr>
                          ) : visibleNoticeRecords.length ? visibleNoticeRecords.map((notice) => (
                            <tr key={notice.id}>
                              <td>
                                <strong>{notice.title_display}</strong><br />
                                <span style={{ fontSize: '.76rem', color: 'var(--text-dim)' }}>{notice.message_preview || 'Attachment-only notice'}</span>
                                <br />
                                <span style={{ fontSize: '.74rem', color: 'var(--text-muted)' }}>By {notice.created_by_name || notice.created_by || 'Unknown'}</span>
                              </td>
                              <td>
                                {(notice.scope_labels || []).slice(0, 3).map((label) => (
                                  <span key={label} className="badge badge-info" style={{ marginRight: 6 }}>{label}</span>
                                ))}
                                {(notice.scope_labels || []).length > 3 ? <span className="badge badge-muted">+{notice.scope_labels.length - 3} more</span> : null}
                              </td>
                              <td>{notice.created_day || '-'}</td>
                              <td>{notice.attachment_count || 0}</td>
                              <td>
                                <span className={`badge ${notice.completion_status === 'completed' ? 'badge-success' : 'badge-warning'}`}>
                                  {notice.completion_status === 'completed' ? 'Completed' : 'Pending'}
                                </span>
                              </td>
                              <td>
                                <div style={{ fontSize: '.8rem' }}>{notice.completed_counselors || 0}/{notice.total_counselors || 0} counselors</div>
                                <div style={{ fontSize: '.76rem', color: 'var(--text-dim)' }}>{notice.sent_students || 0}/{notice.total_students || 0} students</div>
                              </td>
                              <td>
                                <div className="btn-group">
                                  {notice.can_manage_fully ? (
                                    <>
                                      <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleEditNotice(notice.id)}>
                                        <i className="fas fa-pen"></i> Edit
                                      </button>
                                      <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteNoticeAction(notice)}>
                                        <i className="fas fa-trash"></i> Delete
                                      </button>
                                    </>
                                  ) : (
                                    <span className="badge badge-info">Scoped View</span>
                                  )}
                                </div>
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No notices found for the selected filters.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>
                </>
              ) : null}
            </>
          ) : currentUser.role === 'counselor' && activeTab === 'message-history' ? (
            <>
              <div className="metrics-grid mb-3">
                <div className="metric-card">
                  <div className="metric-label">Total Messages</div>
                  <div className="metric-value">{counselorMessageStats?.total ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-envelope"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Today</div>
                  <div className="metric-value">{counselorMessageStats?.today ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-calendar-day"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">This Week</div>
                  <div className="metric-value">{counselorMessageStats?.week ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-calendar-week"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Unique Students</div>
                  <div className="metric-value">{counselorMessageStats?.unique ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-users"></i></div>
                </div>
              </div>

              <div className="card">
                <div className="card-title"><i className="fas fa-envelope-open-text"></i> Message History</div>
                <div className="table-wrapper">
                  <table>
                    <thead>
                      <tr>
                        <th>Date</th>
                        <th>Student Name</th>
                        <th>Reg No</th>
                        <th>Status</th>
                        <th>Mode</th>
                      </tr>
                    </thead>
                    <tbody>
                      {counselorMessagesLoading ? (
                        <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 20 }}>Loading messages...</td></tr>
                      ) : counselorMessages.length ? counselorMessages.map((message) => (
                        <tr key={message.id}>
                          <td>{(message.sent_at || '').slice(0, 16) || '-'}</td>
                          <td>{message.student_name || '-'}</td>
                          <td>{message.reg_no || '-'}</td>
                          <td>
                            <span className={`badge ${String(message.status || '').toLowerCase() === 'sent' ? 'badge-success' : 'badge-warning'}`}>
                              {message.status || 'Pending'}
                            </span>
                          </td>
                          <td>
                            <span className={`badge ${String(message.send_mode || 'app').toLowerCase() === 'web' ? 'badge-info' : 'badge-primary'}`}>
                              {String(message.send_mode || 'app').toUpperCase()}
                            </span>
                          </td>
                        </tr>
                      )) : (
                        <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 20 }}>No message logs available yet.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>
              </div>
            </>
          ) : ['admin', 'hod', 'deo'].includes(currentUser.role) && activeTab === 'messages' ? (
            <Suspense fallback={<div className="card"><div className="panel-placeholder">Loading messages workspace...</div></div>}>
              <MessagesTab
                adminMessagesLoading={adminMessagesLoading}
                adminMessagesData={adminMessagesData}
                adminMessageFilters={adminMessageFilters}
                adminMessageSearch={adminMessageSearch}
                selectedAdminMessageIds={selectedAdminMessageIds}
                SmartDateInput={SmartDateInput}
                onReloadAdminMessages={(filters) => void reloadAdminMessages(filters)}
                onAdminMessageDayChange={(nextValue) => setAdminMessageFilters((prev) => ({
                  ...prev,
                  day: nextValue,
                  year: '',
                  month: '',
                  day_num: '',
                }))}
                onAdminMessageSearchChange={(nextValue) => {
                  startTransition(() => {
                    setAdminMessageSearch(nextValue);
                    setAdminMessageFilters((prev) => ({ ...prev, q: nextValue.trim() }));
                  });
                }}
                onResetAdminMessageFilters={() => {
                  const next = { day: '', q: '', year: '', month: '', day_num: '' };
                  setAdminMessageFilters(next);
                  setAdminMessageSearch('');
                  void reloadAdminMessages(next);
                }}
                onPickAdminMessageDay={(day) => {
                  const next = { ...adminMessageFilters, day };
                  setAdminMessageFilters(next);
                  void reloadAdminMessages(next);
                }}
                onToggleSelectAll={(checked) => setSelectedAdminMessageIds(
                  checked ? (adminMessagesData?.messages || []).map((message) => message.id) : [],
                )}
                onToggleSelectMessage={(id, checked) => setSelectedAdminMessageIds((prev) => (
                  checked ? [...prev, id] : prev.filter((currentId) => currentId !== id)
                ))}
                onDeleteSelected={() => void handleDeleteSelectedAdminMessages()}
                onDeleteMessage={(id) => void handleDeleteAdminMessage(id)}
                onLoadMore={() => {
                  const nextLimit = adminMessagesLimit + ADMIN_MESSAGES_LIMIT_STEP;
                  void loadAdminMessages(adminMessageFilters, nextLimit);
                }}
              />
            </Suspense>
          ) : ['admin', 'principal', 'deo'].includes(currentUser.role) && activeTab === 'users' ? (
            <Suspense fallback={<div className="card"><div className="panel-placeholder">Loading users workspace...</div></div>}>
              <UsersTab
                currentUserRole={currentUser.role}
                metrics={bootstrap?.metrics || null}
                filteredUsers={filteredUsers}
                usersLoading={usersLoading}
                userSearch={userSearch}
                onUserSearchChange={(value) => startTransition(() => setUserSearch(value))}
                userFilterTrayOpen={userFilterTrayOpen}
                onToggleFilterTray={() => setUserFilterTrayOpen((prev) => !prev)}
                onRefreshUsers={() => void refreshUsersOverview({ preferCache: false })}
                userSortBy={userSortBy}
                onUserSortChange={setUserSortBy}
                userFilterDepartment={userFilterDepartment}
                onUserFilterDepartmentChange={setUserFilterDepartment}
                userFilterRole={userFilterRole}
                onUserFilterRoleChange={setUserFilterRole}
                userFilterStatus={userFilterStatus}
                onUserFilterStatusChange={setUserFilterStatus}
                userFilterYear={userFilterYear}
                onUserFilterYearChange={setUserFilterYear}
                userFilterStudentList={userFilterStudentList}
                onUserFilterStudentListChange={setUserFilterStudentList}
                onResetUserFilters={() => {
                  setUserFilterDepartment('');
                  setUserFilterRole('');
                  setUserFilterStatus('');
                  setUserFilterYear('');
                  setUserFilterStudentList('');
                  setUserSortBy('name_asc');
                }}
                userSelectableDepartments={userSelectableDepartments}
                userScopeOptions={userScopeOptions}
                getRoleBadgeClass={getRoleBadgeClass}
                getRoleOptionLabel={getRoleOptionLabel}
                formatYearLevel={formatYearLevel}
                onOpenEditUserModal={openEditUserModal}
                onSetUserActionTarget={(kind, user) => setUserActionTarget({ kind, user })}
                onManageLinkedUsers={setLinkedUserGroupEmail}
                userAssignableRoles={userAssignableRoles}
                userCreateForm={userCreateForm}
                userCreateEmailExists={userCreateEmailExists}
                userCreateEmailDomainValid={userCreateEmailDomainValid}
                userCreateAvailableRoles={userCreateAvailableRoles}
                userCreateExistingName={userCreateExistingAccounts[0]?.name || ''}
                managedUserDomain={managedUserDomain}
                onUserCreateFieldChange={(field, value) => setUserCreateForm((prev) => ({ ...prev, [field]: value }))}
                onUserCreateRoleChange={(role) => setUserCreateForm((prev) => ({
                  ...prev,
                  role,
                  designation: role === 'principal' ? (String(prev.designation || '').trim() || 'Higher Official') : '',
                  scope_pairs: [],
                  department: '',
                  year_level: '1',
                }))}
                onToggleUserCreateScopePair={(value, checked) => setUserCreateForm((prev) => ({
                  ...prev,
                  scope_pairs: checked ? [...prev.scope_pairs, value] : prev.scope_pairs.filter((item) => item !== value),
                }))}
                onCreateUserSubmit={(event) => void handleCreateUser(event)}
                onClearUserCreateForm={handleClearUserCreateDraft}
                userSaving={userSaving}
                bulkCounselorForm={bulkCounselorForm}
                bulkCounselorUploadKey={bulkCounselorUploadKey}
                onBulkCounselorYearChange={(value) => setBulkCounselorForm((prev) => ({ ...prev, year_level: value }))}
                onBulkCounselorFileChange={(file) => setBulkCounselorForm((prev) => ({ ...prev, file }))}
                onBulkCounselorUploadSubmit={(event) => void handleBulkCounselorUpload(event)}
                bulkCounselorSaving={bulkCounselorSaving}
                googleOauthEnabled={String(bootstrap?.appConfig.google_oauth_enabled || 'false').toLowerCase() === 'true'}
              />
            </Suspense>
          ) : (['admin', 'deo'].includes(currentUser.role) && activeTab === 'subjects') ? (
            subjectsLoading && !subjectsData ? (
              <div className="card">
                <div className="panel-placeholder">Loading subjects...</div>
              </div>
            ) : (
              <>
                {subjectsData?.showDepartmentPicker ? (
                  <div className="mb-3">
                    <h3 className="section-title" style={{ marginBottom: 14 }}><i className="fas fa-building"></i> Select Department</h3>
                    <div className="metrics-grid selection-grid department-selection-grid">
                      {(subjectsData?.departments || []).map((department) => (
                        <button
                          key={department.code}
                          type="button"
                          className="metric-card selection-card-button"
                          onClick={() => void loadSubjects(department.code)}
                        >
                          <div className="metric-value" style={{ fontSize: '1.6rem' }}>{department.code}</div>
                          <div className="selection-card-subtitle">{department.name}</div>
                        </button>
                      ))}
                    </div>
                  </div>
                ) : null}

                {subjectsData?.showYearPicker ? (
                  <div className="selection-shell selection-shell-stage-enter mb-3" style={{ maxWidth: 620 }}>
                    <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
                      <ScopeBreadcrumb
                        icon="fa-book-open"
                        items={[
                          { label: 'Subjects', onClick: () => void loadSubjects() },
                          { label: subjectsData.selectedDepartment || 'Department' },
                        ]}
                      />
                    </div>
                    <div className="selection-actions-grid">
                      {(subjectsData.availableYears || []).map((year) => (
                        <button
                          key={year}
                          type="button"
                          className="btn btn-outline selection-action-button"
                          onClick={() => void loadSubjects(subjectsData.selectedDepartment, year)}
                        >
                          {formatYearLevel(year)}
                        </button>
                      ))}
                    </div>
                  </div>
                ) : null}

                {subjectsData?.showSemesterPicker ? (
                  <div className="selection-shell selection-shell-stage-enter mb-3" style={{ maxWidth: 620 }}>
                    <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
                      <ScopeBreadcrumb
                        icon="fa-book-open"
                        items={[
                          { label: 'Subjects', onClick: () => void loadSubjects() },
                          { label: subjectsData.selectedDepartment, onClick: () => void loadSubjects(subjectsData.selectedDepartment) },
                          { label: formatYearLevel(subjectsData.selectedYear || 1) },
                        ]}
                      />
                    </div>
                    <div className="selection-actions-grid">
                      {(subjectsData.availableSemesters || []).map((semester) => (
                        <button
                          key={semester}
                          type="button"
                          className="btn btn-outline selection-action-button"
                          onClick={() => void loadSubjects(subjectsData.selectedDepartment, subjectsData.selectedYear, semester)}
                        >
                          {getSemesterLabel(semester)}
                        </button>
                      ))}
                    </div>
                  </div>
                ) : null}

                {subjectsData && !subjectsData.showDepartmentPicker && !subjectsData.showYearPicker && !subjectsData.showSemesterPicker ? (
                  <>
                    <div className="selection-shell mb-3" style={{ maxWidth: 780 }}>
                      <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12 }}>
                        <ScopeBreadcrumb
                          icon="fa-book-open"
                        items={[
                          { label: 'Subjects', onClick: () => void loadSubjects() },
                          { label: subjectsData.selectedDepartment, onClick: () => void loadSubjects(subjectsData.selectedDepartment) },
                          { label: formatYearLevel(subjectsData.selectedYear || 1), onClick: () => void loadSubjects(subjectsData.selectedDepartment, subjectsData.selectedYear) },
                          { label: getSemesterLabel(subjectsData.selectedSemester || '1'), onClick: () => void loadSubjects(subjectsData.selectedDepartment, subjectsData.selectedYear) },
                        ]}
                      />
                        <button
                          type="button"
                          className="btn btn-outline btn-sm"
                          onClick={() => {
                            setActiveTab('cdp');
                            void loadCdpOverview({
                              department: subjectsData.selectedDepartment,
                              year: subjectsData.selectedYear,
                              semester: subjectsData.selectedSemester,
                            });
                          }}
                        >
                          <i className="fas fa-arrow-right"></i> Open CDP
                        </button>
                      </div>
                    </div>

                    {subjectsData.canManage ? (
                      <div className="card mb-3" style={{ maxWidth: 860 }}>
                        <div className="card-title"><i className="fas fa-book-medical"></i> {subjectEditId ? 'Edit Subject' : 'Create Subject'}</div>
                        <form onSubmit={(event) => void handleSaveSubject(event)}>
                          <div className="form-row">
                            <div className="form-group" style={{ maxWidth: 180 }}>
                              <label className="form-label">Attendance Start Year</label>
                              <input className="form-control" type="number" min="2000" max="2100" value={subjectForm.academic_start_year} onChange={(event) => setSubjectForm((prev) => ({ ...prev, academic_start_year: event.target.value }))} required />
                            </div>
                            <div className="form-group" style={{ maxWidth: 180 }}>
                              <label className="form-label">Attendance End Year</label>
                              <input className="form-control" type="number" min="2000" max="2101" value={subjectForm.academic_end_year} onChange={(event) => setSubjectForm((prev) => ({ ...prev, academic_end_year: event.target.value }))} required />
                            </div>
                          </div>
                          <div className="inline-muted" style={{ marginTop: -8, marginBottom: 12 }}>
                            Daily Attendance dates from months `01-12` use this attendance year range. Example: `2025` to `2026`, or `2025` to `2025` when the sheet stays inside one calendar year.
                          </div>
                          <div className="form-row">
                            <div className="form-group">
                              <label className="form-label">Subject Code</label>
                              <input className="form-control" value={subjectForm.subject_code} onChange={(event) => setSubjectForm((prev) => ({ ...prev, subject_code: event.target.value }))} placeholder="CS3491" required />
                            </div>
                            <div className="form-group">
                              <label className="form-label">Faculty Name</label>
                              <input
                                className="form-control"
                                value={subjectForm.faculty_name}
                                onChange={(event) => setSubjectForm((prev) => {
                                  const nextFacultyName = event.target.value;
                                  const visibleFaculties = splitFacultyNames(nextFacultyName).length
                                    ? splitFacultyNames(nextFacultyName)
                                    : subjectParsedFaculties;
                                  const nextAllocations = normalizeFacultyAllocations(prev.faculty_allocations, visibleFaculties, subjectParsedClasses);
                                  return {
                                    ...prev,
                                    faculty_name: nextFacultyName,
                                    class_sections: normalizeClassSections(nextAllocations.flatMap((entry) => entry.class_sections)),
                                    faculty_allocations: nextAllocations,
                                  };
                                })}
                                placeholder="Dr. Faculty Name"
                                required
                              />
                            </div>
                          </div>
                          <div className="form-row">
                            <div className="form-group">
                              <label className="form-label">Subject Name</label>
                              <input className="form-control" value={subjectForm.subject_name} onChange={(event) => setSubjectForm((prev) => ({ ...prev, subject_name: event.target.value }))} placeholder="Database Management Systems" required />
                            </div>
                            <div className="form-group">
                              <label className="form-label">Google Sheet Link</label>
                              <div className="position-relative">
                                <input
                                  className="form-control"
                                  value={subjectForm.google_sheet_link}
                                  onChange={(event) => setSubjectForm((prev) => ({
                                    ...prev,
                                    google_sheet_link: event.target.value,
                                    class_sections: String(prev.google_sheet_link || '').trim() === String(event.target.value || '').trim()
                                      ? prev.class_sections
                                      : [],
                                    faculty_allocations: String(prev.google_sheet_link || '').trim() === String(event.target.value || '').trim()
                                      ? prev.faculty_allocations
                                      : [],
                                  }))}
                                  placeholder="https://docs.google.com/spreadsheets/..."
                                />
                              </div>
                              <div className="inline-muted" style={{ marginTop: 8 }}>
                                {subjectParsing ? (
                                  <><i className="fas fa-spinner fa-spin"></i> Detecting subject details and class sections from the Daily Attendance sheet...</>
                                ) : subjectParseError ? (
                                  <span style={{ color: 'var(--danger-color)' }}>{subjectParseError}</span>
                                ) : subjectParsedClasses.length ? (
                                  <><i className="fas fa-check-circle" style={{ color: 'var(--success-color)' }}></i> Detected classes: {subjectParsedClasses.join(', ')}</>
                                ) : (
                                  'Paste a Google Sheet link to auto-detect the subject details and available class sections.'
                                )}
                              </div>
                            </div>
                          </div>
                          {subjectParsedClasses.length ? (
                            <div className="card mb-2" style={{ padding: 12, background: 'rgba(59,130,246,.08)', border: '1px solid rgba(59,130,246,.24)' }}>
                              <div className="card-title" style={{ fontSize: '.86rem', marginBottom: 10 }}><i className="fas fa-layer-group"></i> Allocated Classes</div>
                              <div className="inline-muted" style={{ marginBottom: 10 }}>
                                Parsed sections are assigned per faculty. A class can be selected for more than one faculty when they share responsibility.
                              </div>
                              <div style={{ display: 'grid', gap: 12 }}>
                                {(subjectForm.faculty_allocations.length ? subjectForm.faculty_allocations : normalizeFacultyAllocations([], subjectParsedFaculties.length ? subjectParsedFaculties : splitFacultyNames(subjectForm.faculty_name), subjectParsedClasses)).map((allocation) => (
                                  <div key={allocation.faculty_name} className="card" style={{ padding: 12, marginBottom: 0 }}>
                                    <div className="card-title" style={{ fontSize: '.85rem', marginBottom: 10 }}>
                                      <i className="fas fa-user-tie"></i> {allocation.faculty_name}
                                    </div>
                                    <div className="scope-grid">
                                      {subjectParsedClasses.map((sectionLabel) => (
                                        <label key={`${allocation.faculty_name}:${sectionLabel}`} className="scope-chip">
                                          <input
                                            type="checkbox"
                                            checked={allocation.class_sections.includes(sectionLabel)}
                                            onChange={(event) => setSubjectForm((prev) => {
                                              const nextAllocations = prev.faculty_allocations.map((entry) => (
                                                entry.faculty_name !== allocation.faculty_name
                                                  ? entry
                                                  : {
                                                    ...entry,
                                                    class_sections: event.target.checked
                                                      ? normalizeClassSections([...entry.class_sections, sectionLabel])
                                                      : entry.class_sections.filter((value) => value !== sectionLabel),
                                                  }
                                              ));
                                              return {
                                                ...prev,
                                                faculty_allocations: nextAllocations,
                                                class_sections: normalizeClassSections(nextAllocations.flatMap((entry) => entry.class_sections)),
                                              };
                                            })}
                                          />
                                          <span>{sectionLabel}</span>
                                        </label>
                                      ))}
                                    </div>
                                  </div>
                                ))}
                              </div>
                            </div>
                          ) : null}
                          <div className="ui-preview-note" style={{ marginBottom: 12 }}>
                            Scope: <strong>{subjectsData.selectedDepartment}</strong> / <strong>{formatYearLevel(subjectsData.selectedYear || 1)}</strong> / <strong>{getSemesterLabel(subjectsData.selectedSemester || '1')}</strong>. Paste the Google Sheet link to auto-fill subject code, subject name, faculty names, and only the class sections actually parsed from the Daily Attendance sheet. Academic years and faculty-wise allocated classes are required because the daily attendance parser uses them to resolve messy date columns and faculty responsibility.
                          </div>
                          <div className="btn-group">
                            <button type="submit" className="btn btn-primary" disabled={subjectSaving}>
                              <i className={`fas ${subjectSaving ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> {subjectEditId ? 'Save Subject' : 'Create Subject'}
                            </button>
                            {subjectEditId ? (
                              <button type="button" className="btn btn-outline" onClick={() => resetSubjectDraft()}>
                                <i className="fas fa-xmark"></i> Cancel
                              </button>
                            ) : null}
                          </div>
                        </form>
                      </div>
                    ) : (
                      <div className="card mb-3" style={{ maxWidth: 780 }}>
                        <div className="card-title"><i className="fas fa-eye"></i> Read-only Subject Scope</div>
                        <div className="inline-muted">
                          Higher Official access is view-only for Subjects. Use the CDP tab to inspect operational status for this scope.
                        </div>
                      </div>
                    )}

                    <div className="card">
                      <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                        <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-list"></i> Allocated Subjects</div>
                        <span className="badge badge-info">{subjectsData.records.length} subject{subjectsData.records.length === 1 ? '' : 's'}</span>
                      </div>
                      {subjectsData.records.length ? (
                <div className="table-wrapper table-scroll-lg">
                  <table className="sticky-table">
                            <thead>
                              <tr>
                                <th>Code</th>
                                <th>Subject</th>
                                <th>Faculty</th>
                                <th>Semester / Classes</th>
                                <th>Updated</th>
                                <th>Actions</th>
                              </tr>
                            </thead>
                            <tbody>
                              {subjectsData.records.map((subject) => (
                                <tr key={subject.id}>
                                  <td><strong>{subject.subject_code}</strong></td>
                                  <td>{subject.subject_name}</td>
                                  <td>
                                    <div>{subject.faculty_name}</div>
                                    {subject.faculty_allocations.length ? (
                                      <div className="inline-muted" style={{ marginTop: 4 }}>
                                        {subject.faculty_allocations.map((entry) => `${entry.faculty_name}: ${entry.class_sections.join(', ') || 'No classes'}`).join(' | ')}
                                      </div>
                                    ) : null}
                                  </td>
                                  <td>
                                    <span className="inline-muted">{getSemesterLabel(subject.semester)}<br />{subject.class_sections.length ? subject.class_sections.join(', ') : 'All classes'}</span>
                                  </td>
                                  <td style={{ fontSize: '.82rem' }}>{formatDateTime(subject.updated_at || subject.created_at || '')}</td>
                                  <td>
                                    <div className="btn-group">
                                      {subject.google_sheet_link ? (
                                        <a href={subject.google_sheet_link} target="_blank" rel="noreferrer" className="btn btn-outline btn-sm">
                                          <i className="fas fa-link"></i> Sheet
                                        </a>
                                      ) : null}
                                      <button
                                        type="button"
                                        className="btn btn-outline btn-sm"
                                        onClick={() => {
                                          setActiveTab('cdp');
                                          void rebuildCdpScopeOverview({
                                            department: subject.department,
                                            year: subject.year_level,
                                            semester: subject.semester,
                                            subject_id: subject.id,
                                          });
                                        }}
                                      >
                                        <i className="fas fa-arrow-up-right-from-square"></i> CDP
                                      </button>
                                      {subjectsData.canManage ? (
                                        <>
                                          <button type="button" className="btn btn-outline btn-sm" onClick={() => beginSubjectEdit(subject)}>
                                            <i className="fas fa-edit"></i> Edit
                                          </button>
                                          <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteSubject(subject)}>
                                            <i className="fas fa-trash"></i>
                                          </button>
                                        </>
                                      ) : null}
                                    </div>
                                  </td>
                                </tr>
                              ))}
                            </tbody>
                          </table>
                        </div>
                      ) : (
                        <div className="panel-placeholder">No subjects are configured yet for this department/year scope.</div>
                      )}
                    </div>
                  </>
                ) : null}
              </>
            )
          ) : (['admin', 'principal', 'hod'].includes(currentUser.role) && activeTab === 'cdp') ? (
            <Suspense fallback={<div className="card"><div className="panel-placeholder">Loading CDP workspace...</div></div>}>
              <CdpTab
                cdpLoading={cdpLoading}
                cdpData={cdpData}
                ScopeBreadcrumb={ScopeBreadcrumb}
                formatYearLevel={formatYearLevel}
                formatDateTime={formatDateTime}
                getSemesterLabel={getSemesterLabel}
                onLoadCdpOverview={(filters) => void loadCdpOverview(filters)}
                onRebuildScope={(filters) => void rebuildCdpScopeOverview(filters)}
                copyTemplate={String(bootstrap?.appConfig?.cdp_defaulter_copy_template || DEFAULT_CDP_DEFAULTER_COPY_TEMPLATE)}
                onShowNoDefaultersNotice={(message) => {
                  setFlash({ type: 'warning', message });
                }}
                onShowCopyDialog={(title, message) => {
                  setConfirmDialog({
                    title,
                    message,
                    confirmLabel: 'OK',
                    confirmClassName: title === 'Copy Failed' ? 'btn btn-danger btn-sm' : 'btn btn-primary btn-sm',
                    iconClassName: title === 'Copy Failed' ? 'fas fa-circle-exclamation' : 'fas fa-copy',
                    cancelLabel: null,
                  });
                }}
              />
            </Suspense>
          ) : (['admin', 'principal', 'hod', 'deo'].includes(currentUser.role) && activeTab === 'activity') ? (
            <Suspense fallback={<div className="card"><div className="panel-placeholder">Loading counselor activity workspace...</div></div>}>
              <ActivityTab
                activityLoading={activityLoading}
                activityCopying={activityCopying}
                activityPdfLoading={activityPdfLoading}
                activityData={activityData}
                activityDisplayRows={activityDisplayRows}
                activityFilters={activityFilters}
                ScopeBreadcrumb={ScopeBreadcrumb}
                formatYearLevel={formatYearLevel}
                formatDateTime={formatDateTime}
                onLoadActivityOverview={(filters) => void loadActivityOverview(filters)}
                onActivitySearchChange={(value) => startTransition(() => setActivityFilters((prev) => ({ ...prev, q: value })))}
                onActivitySortChange={(value) => setActivityFilters((prev) => ({ ...prev, sort: value }))}
                onResetActivityToRoot={() => {
                  setActivityFilters({ department: '', year: '', semester: '', test_name: '', q: '', sort: 'pending_first' });
                  void loadActivityOverview();
                }}
                onCopyActivityDefaulters={(mode, options) => void handleCopyActivityDefaulters(mode, options)}
                onDownloadActivityScopePdf={() => void handleDownloadActivityScopePdf()}
              />
            </Suspense>
          ) : (['admin', 'principal'].includes(currentUser.role) && activeTab === 'database') ? (
            <>
              {currentUser.role === 'admin' ? (
                <div className="card mb-3" style={{ maxWidth: 780 }}>
                  <div className="card-title"><i className="fas fa-floppy-disk"></i> Create Backup</div>
                  <p style={{ fontSize: '.85rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                    Create a full database backup before batch operations.
                  </p>
                  <form onSubmit={(event) => void handleCreateBackup(event)} className="form-row" style={{ alignItems: 'end' }}>
                    <div className="form-group">
                      <label className="form-label">Batch Label</label>
                      <input className="form-control" value={databaseBatchName} onChange={(event) => setDatabaseBatchName(event.target.value)} placeholder="2025-2026" required disabled={archiveViewActive || databaseBackupCreating} />
                    </div>
                    <label className="form-check" style={{ marginBottom: 10 }}>
                      <input type="checkbox" checked={databaseOverwrite} onChange={(event) => setDatabaseOverwrite(event.target.checked)} disabled={archiveViewActive || databaseBackupCreating} />
                      <span>Overwrite if same label exists</span>
                    </label>
                    <div className="form-group">
                      <button className="btn btn-primary" type="submit" disabled={archiveViewActive || databaseBackupCreating}>
                        <i className={`fas ${databaseBackupCreating ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> {databaseBackupCreating ? 'Creating Backup...' : 'Create Backup'}
                      </button>
                    </div>
                  </form>
                </div>
              ) : (
                <div className="card mb-3" style={{ maxWidth: 780 }}>
                  <div className="card-title"><i className="fas fa-eye"></i> Archive Viewer</div>
                  <p style={{ fontSize: '.85rem', color: 'var(--text-dim)', marginBottom: 0 }}>
                    Higher Officials can open archived academic years in read-only mode from the archive list below.
                  </p>
                </div>
              )}

              {databaseLoading && !databaseData ? (
                <div className="card"><div className="panel-placeholder">Loading database tools...</div></div>
              ) : (
                <>
                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-clock-rotate-left"></i> Automatic Backups (Daily)</div>
                  <div className="table-wrapper table-scroll-lg">
                    <table className="sticky-table">
                        <thead>
                          <tr>
                            <th>Backup</th>
                            <th>Size</th>
                            <th>Modified</th>
                            <th style={{ textAlign: 'right' }}>Actions</th>
                          </tr>
                        </thead>
                        <tbody>
                          {(databaseData?.autoBackupFiles || []).length ? databaseData!.autoBackupFiles.map((backup) => (
                            <tr key={backup.name}>
                              <td><strong>{backup.name}</strong></td>
                              <td>{backup.size_kb} KB</td>
                              <td>{backup.modified}</td>
                              <td style={{ textAlign: 'right' }}>
                                {currentUser.role === 'admin' ? (
                                  <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                                    <button type="button" className="btn btn-outline btn-sm" disabled={archiveViewActive} onClick={() => { setDatabaseBackupAction({ kind: 'restore', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                      <i className="fas fa-rotate-left"></i> Restore
                                    </button>
                                    <button type="button" className="btn btn-danger btn-sm" disabled={archiveViewActive} onClick={() => { setDatabaseBackupAction({ kind: 'delete', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                      <i className="fas fa-trash"></i> Delete
                                    </button>
                                  </div>
                                ) : (
                                  <span className="text-muted">Read only</span>
                                )}
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={4} className="text-center text-muted" style={{ padding: 20 }}>No automatic backups available.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-box-archive"></i> Existing Backups</div>
                    <div className="inline-muted" style={{ marginBottom: 12 }}>
                      Current storage mode: {databaseData?.backupStorageMode === 'gdrive' ? 'Google Drive' : 'Local rebuild storage'}
                    </div>
                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>Backup</th>
                            <th>Size</th>
                            <th>Modified</th>
                            <th style={{ textAlign: 'right' }}>Actions</th>
                          </tr>
                        </thead>
                        <tbody>
                          {(databaseData?.backupFiles || []).length ? databaseData!.backupFiles.map((backup) => (
                            <tr key={backup.name}>
                              <td><strong>{backup.name}</strong></td>
                              <td>{backup.size_kb} KB</td>
                              <td>{backup.modified}</td>
                              <td style={{ textAlign: 'right' }}>
                                {currentUser.role === 'admin' ? (
                                  <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                                    <button type="button" className="btn btn-outline btn-sm" disabled={archiveViewActive} onClick={() => { setDatabaseBackupAction({ kind: 'restore', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                      <i className="fas fa-rotate-left"></i> Restore
                                    </button>
                                    <button type="button" className="btn btn-danger btn-sm" disabled={archiveViewActive} onClick={() => { setDatabaseBackupAction({ kind: 'delete', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                      <i className="fas fa-trash"></i> Delete
                                    </button>
                                  </div>
                                ) : (
                                  <span className="text-muted">Read only</span>
                                )}
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={4} className="text-center text-muted" style={{ padding: 20 }}>No backups available.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-warehouse"></i> Year Archives</div>
                    <div className="inline-muted" style={{ marginBottom: 12 }}>
                      Archives are stored separately from active backups so each academic year snapshot stays isolated.
                    </div>
                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>Academic Year</th>
                            <th>Modified</th>
                            <th style={{ textAlign: 'right' }}>Actions</th>
                          </tr>
                        </thead>
                        <tbody>
                          {(databaseData?.archiveFiles || []).length ? databaseData!.archiveFiles.map((archive) => (
                            <tr key={archive.name}>
                              <td><strong>{archive.academic_year_label || archive.name}</strong></td>
                              <td>{archive.modified}</td>
                              <td style={{ textAlign: 'right' }}>
                                <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleEnterArchiveView(archive.name)}>
                                    <i className="fas fa-eye"></i> View
                                  </button>
                                  {currentUser.role === 'admin' ? (
                                    <>
                                      <button type="button" className="btn btn-outline btn-sm" disabled={archiveViewActive} onClick={() => { setDatabaseBackupAction({ kind: 'restore-archive', backupName: archive.name }); setDatabaseActionPassword(''); }}>
                                        <i className="fas fa-rotate-left"></i> Restore
                                      </button>
                                      <button type="button" className="btn btn-danger btn-sm" disabled={archiveViewActive} onClick={() => { setDatabaseBackupAction({ kind: 'delete-archive', backupName: archive.name }); setDatabaseActionPassword(''); }}>
                                        <i className="fas fa-trash"></i> Delete
                                      </button>
                                    </>
                                  ) : null}
                                </div>
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={3} className="text-center text-muted" style={{ padding: 20 }}>No year archives available yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  {currentUser.role === 'admin' ? (
                    <div className="form-row" style={{ alignItems: 'stretch' }}>
                      <div className="card" style={{ border: '1px solid rgba(220,38,38,.35)' }}>
                        <div className="card-title"><i className="fas fa-box-archive"></i> Archive Year</div>
                        <p style={{ fontSize: '.85rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                          Creates a year archive in the rebuild archive folder, then clears active operational data while retaining Admin and Higher Official access. Password confirmation is requested in the warning popup.
                        </p>
                        <form onSubmit={(event) => void handleArchiveYear(event)}>
                          <div className="form-row">
                            <div className="form-group">
                              <label className="form-label">Start Year</label>
                              <input
                                className="form-control"
                                inputMode="numeric"
                                pattern="\d{4}"
                                value={archiveYearStart}
                                onChange={(event) => setArchiveYearStart(event.target.value.replace(/[^\d]/g, '').slice(0, 4))}
                                required
                                placeholder="2025"
                                disabled={archiveViewActive}
                              />
                            </div>
                            <div className="form-group">
                              <label className="form-label">End Year</label>
                              <input
                                className="form-control"
                                inputMode="numeric"
                                pattern="\d{4}"
                                value={archiveYearEnd}
                                onChange={(event) => setArchiveYearEnd(event.target.value.replace(/[^\d]/g, '').slice(0, 4))}
                                required
                                placeholder="2026"
                                disabled={archiveViewActive}
                              />
                            </div>
                          </div>
                          <div className="inline-muted" style={{ marginBottom: 12 }}>
                            Archive label: {archiveYearLabel || 'Enter both years'}
                          </div>
                          <label className="form-check" style={{ marginBottom: 12 }}>
                            <input type="checkbox" checked={archiveYearOverwrite} onChange={(event) => setArchiveYearOverwrite(event.target.checked)} disabled={archiveViewActive} />
                            <span>Overwrite if this academic year archive already exists</span>
                          </label>
                          <button className="btn btn-danger" type="submit" disabled={archiveViewActive}>
                            <i className="fas fa-box-archive"></i> Archive Active Year
                          </button>
                        </form>
                      </div>

                      <div className="card" style={{ border: '1px solid rgba(239,68,68,.35)' }}>
                        <div className="card-title"><i className="fas fa-trash-can"></i> Clear Database</div>
                        <p style={{ fontSize: '.85rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                          Clears the current live exam and notice workspace without creating an archive. This action requires your password and follows the existing backup safety checks.
                        </p>
                        <div className="inline-muted" style={{ marginBottom: 14 }}>
                          Use this only when you want a clean active workspace immediately.
                        </div>
                        <button
                          className="btn btn-danger"
                          type="button"
                          disabled={archiveViewActive}
                          onClick={() => {
                            setDatabaseActionPassword('');
                            setDatabaseBackupAction({ kind: 'clear', backupName: 'active workspace' });
                          }}
                        >
                          <i className="fas fa-trash-can"></i> Clear Active Database
                        </button>
                      </div>
                    </div>
                  ) : null}
                </>
              )}
            </>
          ) : (currentUser.role === 'admin' && activeTab === 'monitoring') ? (
            <Suspense fallback={<div className="card"><div className="panel-placeholder">Loading session monitoring workspace...</div></div>}>
              <MonitoringTab
                currentUserEmail={currentUser.email}
                monitoringData={monitoringData}
                monitoringLoading={monitoringLoading}
                monitoringSearch={monitoringSearch}
                monitoringStatusFilter={monitoringStatusFilter}
                monitoringAuthFilter={monitoringAuthFilter}
                monitoringSortBy={monitoringSortBy}
                filteredMonitoringSessions={filteredMonitoringSessions}
                filteredMonitoringHistory={filteredMonitoringHistory}
                onMonitoringSearchChange={(value) => startTransition(() => setMonitoringSearch(value))}
                onMonitoringStatusFilterChange={setMonitoringStatusFilter}
                onMonitoringAuthFilterChange={setMonitoringAuthFilter}
                onMonitoringSortChange={setMonitoringSortBy}
                onMonitoringReset={() => {
                  setMonitoringSearch('');
                  setMonitoringStatusFilter('all');
                  setMonitoringAuthFilter('all');
                  setMonitoringSortBy('last_activity_desc');
                }}
                onMonitoringRefresh={() => void loadMonitoringOverview()}
                onLogoutAllUsers={() => void handleLogoutAllUsers()}
                onForceLogout={(email) => void handleForceLogout(email)}
                formatUtcSqlDateTime={formatUtcSqlDateTime}
              />
            </Suspense>
          ) : (currentUser.role === 'admin' && activeTab === 'config') ? (
            configLoading && !configData ? (
              <div className="card"><div className="panel-placeholder">Loading settings...</div></div>
            ) : (
              <>
                {runtimeConfig.isDesktop ? (
                  <div className="card mb-3">
                    <div className="form-group" style={{ maxWidth: 360, marginBottom: 0 }}>
                      <label className="form-label">Settings Area</label>
                      <div className="segmented-switch" data-mode={configDesktopMode === 'desktop' ? 'gdrive' : 'local'}>
                        <div className="segmented-switch-thumb" aria-hidden="true"></div>
                        <button type="button" className={`segmented-switch-option ${configDesktopMode === 'server' ? 'active' : ''}`} onClick={() => setConfigDesktopMode('server')}>
                          Server Settings
                        </button>
                        <button type="button" className={`segmented-switch-option ${configDesktopMode === 'desktop' ? 'active' : ''}`} onClick={() => {
                          setConfigDesktopMode('desktop');
                          void loadDesktopRuntimeState();
                        }}>
                          Desktop App
                        </button>
                      </div>
                    </div>
                  </div>
                ) : null}

                {runtimeConfig.isDesktop && configDesktopMode === 'desktop' ? renderDesktopAppSettingsPanel() : (
                <form onSubmit={(event) => void handleSaveConfig(event)}>
                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-file-arrow-up"></i> Configuration Migration</div>
                    <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                      Export the full Shine rebuild settings package for migration, or import a previously downloaded config file into this instance.
                    </p>
                    <div className="btn-group" style={{ gap: 10, flexWrap: 'wrap' }}>
                      <button type="button" className="btn btn-outline" onClick={() => void handleDownloadConfigExport()}>
                        <i className="fas fa-download"></i> Download Config
                      </button>
                      <button type="button" className="btn btn-primary" disabled={configImporting} onClick={() => configImportInputRef.current?.click()}>
                        <i className={`fas ${configImporting ? 'fa-spinner fa-spin' : 'fa-upload'}`}></i> {configImporting ? 'Importing...' : 'Upload Config'}
                      </button>
                    </div>
                    <input
                      ref={configImportInputRef}
                      type="file"
                      accept="application/json,.json"
                      style={{ display: 'none' }}
                      onChange={(event) => void handleImportConfigFile(event)}
                    />
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-paper-plane"></i> Counselor Messaging Controls</div>
                    <label className="form-check">
                      <input type="checkbox" checked={Boolean(configForm.enable_counselor_batch_send)} onChange={(event) => setConfigForm((prev) => ({ ...prev, enable_counselor_batch_send: event.target.checked }))} />
                      <span>Enable Batch Send for Counselors</span>
                    </label>
                    <div className="form-group" style={{ marginTop: 12, maxWidth: 220 }}>
                      <label className="form-label">Batch Send Delay (seconds)</label>
                      <input type="number" min="1" max="30" step="1" className="form-control" value={String(configForm.counselor_batch_send_delay_seconds || '4')} onChange={(event) => setConfigForm((prev) => ({ ...prev, counselor_batch_send_delay_seconds: event.target.value }))} />
                    </div>
                    <div className="settings-slider-row" style={{ marginTop: 12 }}>
                      <div>
                        <div className="form-label" style={{ marginBottom: 4 }}>Enable desktop send workspace in Windows app</div>
                        <div className="inline-muted" style={{ fontSize: '.78rem' }}>
                          Enables the Windows-only floating/send workspace for new result and notice sending sessions.
                        </div>
                      </div>
                      <label className="settings-slider" aria-label="Enable desktop send workspace in Windows app">
                        <input
                          type="checkbox"
                          checked={Boolean(configForm.desktop_send_workspace_enabled)}
                          onChange={(event) => setConfigForm((prev) => ({ ...prev, desktop_send_workspace_enabled: event.target.checked }))}
                        />
                        <span className="settings-slider-track" aria-hidden="true"></span>
                      </label>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-graduation-cap"></i> Academic Batch Settings</div>
                    <div className="form-row">
                      <div className="form-group" style={{ maxWidth: 240 }}>
                        <label className="form-label">1st Year Batch</label>
                        <input className="form-control" value={String(configForm.current_batch_year || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, current_batch_year: event.target.value }))} placeholder="2025-2026" />
                      </div>
                    </div>
                    <div className="form-row" style={{ gap: 12 }}>
                      {[1, 2, 3, 4].map((year) => (
                        <div key={year} className="form-group" style={{ minWidth: 180 }}>
                          <label className="form-label">{formatYearLevel(year)}</label>
                          <input className="form-control" value={deriveBatchNameFromBase(String(configForm.current_batch_year || ''), year)} readOnly />
                        </div>
                      ))}
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-shield-alt"></i> Session Security Settings</div>
                    <div className="form-group" style={{ maxWidth: 220 }}>
                      <label className="form-label">Session Timeout (hours)</label>
                      <input type="number" min="1" max="168" className="form-control" value={String(configForm.session_timeout_hours || '24')} onChange={(event) => setConfigForm((prev) => ({ ...prev, session_timeout_hours: event.target.value }))} />
                    </div>
                    <div className="form-group" style={{ maxWidth: 260 }}>
                      <label className="form-label">Desktop Notification Poll (seconds)</label>
                      <input type="number" min="10" max="3600" className="form-control" value={String(configForm.desktop_notification_poll_seconds || '30')} onChange={(event) => setConfigForm((prev) => ({ ...prev, desktop_notification_poll_seconds: event.target.value }))} />
                    </div>
                    <div className="form-group" style={{ maxWidth: 280 }}>
                      <label className="form-label">Pending Reminder Threshold (days)</label>
                      <input type="number" min="1" max="30" className="form-control" value={String(configForm.notification_pending_threshold_days || '2')} onChange={(event) => setConfigForm((prev) => ({ ...prev, notification_pending_threshold_days: event.target.value }))} />
                    </div>
                    <label className="form-check">
                      <input type="checkbox" checked={Boolean(configForm.allow_concurrent_sessions)} onChange={(event) => setConfigForm((prev) => ({ ...prev, allow_concurrent_sessions: event.target.checked }))} />
                      <span>Allow Same User on Multiple Devices</span>
                    </label>
                    <div className="form-group" style={{ marginTop: 12, maxWidth: 180 }}>
                      <label className="form-label">Max Concurrent Sessions</label>
                      <input type="number" min="1" max="5" className="form-control" value={String(configForm.max_concurrent_sessions || '1')} onChange={(event) => setConfigForm((prev) => ({ ...prev, max_concurrent_sessions: event.target.value }))} />
                    </div>
                    <label className="form-check" style={{ marginTop: 10 }}>
                      <input type="checkbox" checked={Boolean(configForm.enable_periodic_backups)} onChange={(event) => setConfigForm((prev) => ({ ...prev, enable_periodic_backups: event.target.checked }))} />
                      <span>Enable Periodic Database Backups</span>
                    </label>
                    <div className="form-row" style={{ marginTop: 10 }}>
                      <div className="form-group" style={{ maxWidth: 180 }}>
                        <label className="form-label">Backup Hour (0-23)</label>
                        <input type="number" min="0" max="23" className="form-control" value={String(configForm.periodic_backup_hour || '0')} onChange={(event) => setConfigForm((prev) => ({ ...prev, periodic_backup_hour: event.target.value }))} />
                      </div>
                      <div className="form-group" style={{ maxWidth: 180 }}>
                        <label className="form-label">Backup Minute (0-59)</label>
                        <input type="number" min="0" max="59" className="form-control" value={String(configForm.periodic_backup_minute || '0')} onChange={(event) => setConfigForm((prev) => ({ ...prev, periodic_backup_minute: event.target.value }))} />
                      </div>
                    </div>
                    <label className="form-check" style={{ marginTop: 10 }}>
                      <input type="checkbox" checked={Boolean(configForm.disable_default_admin_on_new_system_admin)} onChange={(event) => setConfigForm((prev) => ({ ...prev, disable_default_admin_on_new_system_admin: event.target.checked }))} />
                      <span>Auto-disable default system admin after creating another system admin</span>
                    </label>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-person-chalkboard"></i> Guided Tutorial Settings</div>
                    <label className="form-check" style={{ marginBottom: 12 }}>
                      <input type="checkbox" checked={Boolean(configForm.tutorial_master_enabled)} onChange={(event) => setConfigForm((prev) => ({ ...prev, tutorial_master_enabled: event.target.checked }))} />
                      <span>Enable Guided Tutorials (Master)</span>
                    </label>
                    <div className="form-row">
                      {[
                        ['tutorial_counselor_enabled', 'Counselor Tutorial'],
                        ['tutorial_hod_enabled', 'HoD Tutorial'],
                        ['tutorial_deo_enabled', 'DEO Tutorial'],
                        ['tutorial_principal_enabled', 'Higher Official Tutorial'],
                      ].map(([key, label]) => (
                        <label key={key} className="form-check" style={{ minWidth: 180 }}>
                          <input
                            type="checkbox"
                            checked={Boolean(configForm[key])}
                            disabled={!Boolean(configForm.tutorial_master_enabled)}
                            onChange={(event) => setConfigForm((prev) => ({ ...prev, [key]: event.target.checked }))}
                          />
                          <span>{label}</span>
                        </label>
                      ))}
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-user-shield"></i> OTP Security Policy</div>
                    <label className="form-check" style={{ marginBottom: 10 }}>
                      <input type="checkbox" checked={Boolean(configForm.require_otp_on_password_reset)} onChange={(event) => setConfigForm((prev) => ({ ...prev, require_otp_on_password_reset: event.target.checked }))} />
                      <span>Require OTP for password reset (except default admin)</span>
                    </label>
                    <label className="form-check" style={{ marginBottom: 10 }}>
                      <input type="checkbox" checked={Boolean(configForm.require_otp_on_login)} onChange={(event) => setConfigForm((prev) => ({ ...prev, require_otp_on_login: event.target.checked }))} />
                      <span>Require OTP for login (except default admin)</span>
                    </label>
                    <div className="form-group" style={{ maxWidth: 220 }}>
                      <label className="form-label">OTP Lockout (hours)</label>
                      <input
                        type="number"
                        min="1"
                        max="168"
                        className="form-control"
                        value={String(configForm.otp_login_lock_hours || '5')}
                        onChange={(event) => setConfigForm((prev) => ({ ...prev, otp_login_lock_hours: event.target.value }))}
                      />
                      <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', marginTop: 4, display: 'block' }}>
                        Applied after 3 invalid login OTP attempts.
                      </small>
                    </div>
                    {otpPolicyChanged ? (
                      <div className="form-group" style={{ maxWidth: 360 }}>
                        <label className="form-label">Policy Change Warning</label>
                        <div className="ui-preview-note">
                          Saving this change logs out every active account immediately and will ask for your admin password in the save popup.
                        </div>
                      </div>
                    ) : null}
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-copy"></i> Defaulter Copy Format</div>
                    <label className="form-check" style={{ marginBottom: 10 }}>
                      <input type="checkbox" checked={Boolean(configForm.notice_copy_as_image)} onChange={(event) => setConfigForm((prev) => ({ ...prev, notice_copy_as_image: event.target.checked }))} />
                      <span>Copy Notice Defaulters as styled image</span>
                    </label>
                    <label className="form-check">
                      <input type="checkbox" checked={Boolean(configForm.activity_copy_as_image)} onChange={(event) => setConfigForm((prev) => ({ ...prev, activity_copy_as_image: event.target.checked }))} />
                      <span>Copy Counselor Activity Defaulters as styled image</span>
                    </label>
                    <div className="form-group" style={{ marginTop: 14 }}>
                      <label className="form-label">Notice Copy Template</label>
                      <textarea
                        className="form-control"
                        rows={5}
                        value={String(configForm.notice_defaulter_copy_template || '')}
                        onChange={(event) => setConfigForm((prev) => ({ ...prev, notice_defaulter_copy_template: event.target.value }))}
                        placeholder={DEFAULT_NOTICE_DEFAULTER_COPY_TEMPLATE}
                      />
                      <small style={{ fontSize: '.74rem', color: 'var(--text-dim)' }}>
                        Use {'{entries}'} for the generated notice rows and {'{count}'} for the pending counselor count.
                      </small>
                    </div>
                    <div className="form-group" style={{ marginTop: 12 }}>
                      <label className="form-label">Counsellor Activity Copy Template</label>
                      <textarea
                        className="form-control"
                        rows={5}
                        value={String(configForm.activity_defaulter_copy_template || '')}
                        onChange={(event) => setConfigForm((prev) => ({ ...prev, activity_defaulter_copy_template: event.target.value }))}
                        placeholder={DEFAULT_ACTIVITY_DEFAULTER_COPY_TEMPLATE}
                      />
                      <small style={{ fontSize: '.74rem', color: 'var(--text-dim)' }}>
                        Use {'{entries}'} for the generated activity rows, {'{count}'} for pending counselors, and {'{mode}'} for the copy scope.
                      </small>
                    </div>
                    <div className="form-group" style={{ marginTop: 12 }}>
                      <label className="form-label">CDP Copy Template</label>
                      <textarea
                        className="form-control"
                        rows={5}
                        value={String(configForm.cdp_defaulter_copy_template || '')}
                        onChange={(event) => setConfigForm((prev) => ({ ...prev, cdp_defaulter_copy_template: event.target.value }))}
                        placeholder={DEFAULT_CDP_DEFAULTER_COPY_TEMPLATE}
                      />
                      <small style={{ fontSize: '.74rem', color: 'var(--text-dim)' }}>
                        Use {'{entries}'} for subject blocks, {'{count}'} for pending faculty count, and {'{scope}'} for the selected CDP scope.
                      </small>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-hard-drive"></i> Backup Storage Mode</div>
                    <div className="form-row">
                      <div className="form-group" style={{ maxWidth: 280 }}>
                        <label className="form-label">Storage Target</label>
                        <div className="segmented-switch" data-mode={String(configForm.backup_storage_mode || 'local')}>
                          <div className="segmented-switch-thumb" aria-hidden="true"></div>
                          <button
                            type="button"
                            className={`segmented-switch-option ${String(configForm.backup_storage_mode || 'local') === 'local' ? 'active' : ''}`}
                            onClick={() => setConfigForm((prev) => ({ ...prev, backup_storage_mode: 'local' }))}
                          >
                            Local
                          </button>
                          <button
                            type="button"
                            className={`segmented-switch-option ${String(configForm.backup_storage_mode || 'local') === 'gdrive' ? 'active' : ''}`}
                            onClick={() => setConfigForm((prev) => ({ ...prev, backup_storage_mode: 'gdrive' }))}
                          >
                            Google Drive
                          </button>
                        </div>
                      </div>
                    </div>
                    {String(configForm.backup_storage_mode || 'local') === 'gdrive' ? (
                      <div className="form-row">
                        <div className="form-group">
                          <label className="form-label">Google Drive Refresh Token</label>
                          <input
                            type="password"
                            className="form-control"
                            value={String(configForm.google_drive_refresh_token || '')}
                            onChange={(event) => setConfigForm((prev) => ({ ...prev, google_drive_refresh_token: event.target.value }))}
                            placeholder="Paste the offline refresh token"
                          />
                        </div>
                        <div className="form-group">
                          <label className="form-label">Google Drive Folder ID (Optional)</label>
                          <input
                            className="form-control"
                            value={String(configForm.google_drive_folder_id || '')}
                            onChange={(event) => setConfigForm((prev) => ({ ...prev, google_drive_folder_id: event.target.value }))}
                            placeholder="Drive folder id for backups and archives"
                          />
                        </div>
                      </div>
                    ) : null}
                    <div className="ui-preview-note">
                      Switching modes migrates the rebuild backup folders between local storage and Google Drive using the same plain `.db` files and snapshot folders. The live running database still stays local for reliability, while Drive mirrors the rebuild data structure instead of uploading zip bundles.
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-envelope"></i> SMTP Configuration</div>
                    <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                      {configData?.smtpStatus.label}: {configData?.smtpStatus.detail}
                    </p>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">SMTP Server</label>
                        <input className="form-control" value={String(configForm.smtp_server || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, smtp_server: event.target.value }))} placeholder="smtp.gmail.com" />
                      </div>
                      <div className="form-group" style={{ maxWidth: 120 }}>
                        <label className="form-label">SMTP Port</label>
                        <input type="number" min="1" max="65535" className="form-control" value={String(configForm.smtp_port || '587')} onChange={(event) => setConfigForm((prev) => ({ ...prev, smtp_port: event.target.value }))} />
                      </div>
                    </div>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">SMTP Username</label>
                        <input className="form-control" value={String(configForm.smtp_username || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, smtp_username: event.target.value }))} />
                      </div>
                      <div className="form-group">
                        <label className="form-label">SMTP Password</label>
                        <input type="password" className="form-control" value={String(configForm.smtp_password || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, smtp_password: event.target.value }))} placeholder="Leave blank to keep current" />
                      </div>
                    </div>
                    <div className="form-group">
                      <label className="form-label">From Email Address</label>
                      <input className="form-control" value={String(configForm.email_from || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, email_from: event.target.value }))} placeholder="noreply@rmkcet.ac.in" />
                    </div>
                    <div className="btn-group">
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleRefreshSmtpStatus()}>
                        <i className="fas fa-sync"></i> Refresh SMTP Status
                      </button>
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleRunSmtpTest()} disabled={smtpTesting}>
                        <i className={`fas ${smtpTesting ? 'fa-spinner fa-spin' : 'fa-vial'}`}></i> {smtpTesting ? 'Testing...' : 'Send Test Email'}
                      </button>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fab fa-google"></i> Google OAuth Sign-In</div>
                    <label className="form-check" style={{ marginBottom: 12 }}>
                      <input type="checkbox" checked={Boolean(configForm.google_oauth_enabled)} onChange={(event) => setConfigForm((prev) => ({ ...prev, google_oauth_enabled: event.target.checked }))} />
                      <span>Enable Google OAuth Login</span>
                    </label>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Google Client ID</label>
                        <input className="form-control" value={String(configForm.google_oauth_client_id || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, google_oauth_client_id: event.target.value }))} />
                      </div>
                      <div className="form-group">
                        <label className="form-label">Google Client Secret</label>
                        <input type="password" className="form-control" value={String(configForm.google_oauth_client_secret || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, google_oauth_client_secret: event.target.value }))} placeholder="Leave blank to keep current" />
                      </div>
                    </div>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Allowed Google Domain (Optional)</label>
                        <input className="form-control" value={String(configForm.google_oauth_allowed_domain || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, google_oauth_allowed_domain: event.target.value }))} placeholder="rmkcet.ac.in" />
                      </div>
                      <div className="form-group">
                        <label className="form-label">Redirect Base URL (Optional)</label>
                        <input className="form-control" value={String(configForm.google_oauth_redirect_base_url || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, google_oauth_redirect_base_url: event.target.value }))} placeholder="https://your-domain.example" />
                      </div>
                    </div>
                    <div className="card" style={{ padding: 14, background: 'rgba(255,255,255,.03)', border: '1px solid var(--border)', marginTop: 10 }}>
                      <div className="card-title" style={{ fontSize: '.9rem', marginBottom: 10 }}><i className="fas fa-key"></i> Bulk Counselor Non-OAuth Password Rule</div>
                      <div className="form-row">
                        <div className="form-group">
                          <label className="form-label">Password Source For Bulk Upload</label>
                          <select className="form-control" value={String(configForm.google_oauth_bulk_password_mode || 'sheet')} onChange={(event) => setConfigForm((prev) => ({ ...prev, google_oauth_bulk_password_mode: event.target.value }))}>
                            <option value="sheet">Use Uploaded Sheet Password</option>
                            <option value="override">Use Settings Override Password</option>
                          </select>
                        </div>
                        {String(configForm.google_oauth_bulk_password_mode || 'sheet') === 'override' ? (
                          <div className="form-group">
                            <label className="form-label">Non-OAuth Override Password</label>
                            <input type="password" className="form-control" value={String(configForm.google_oauth_bulk_override_password || '')} onChange={(event) => setConfigForm((prev) => ({ ...prev, google_oauth_bulk_override_password: event.target.value }))} placeholder="Leave blank to keep current" />
                          </div>
                        ) : null}
                      </div>
                    </div>
                  </div>

                  <div className="btn-group mb-3">
                    <button type="submit" className="btn btn-primary" disabled={configSaving}>
                      <i className={`fas ${configSaving ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> {configSaving ? 'Saving...' : 'Save All Settings'}
                    </button>
                    {configFormDirty ? <span className="badge badge-warning" style={{ alignSelf: 'center' }}>Unsaved Changes</span> : null}
                  </div>
                </form>
                )}

                <div className="card mt-3">
                  <div className="card-title"><i className="fas fa-file-code"></i> Raw .env Editor</div>
                  <form onSubmit={(event) => void handleSaveEnvContent(event)}>
                    <div className="form-group">
                      <textarea className="form-control" rows={10} style={{ fontFamily: 'monospace', fontSize: '.85rem', lineHeight: 1.5 }} value={envDraft} onChange={(event) => setEnvDraft(event.target.value)} />
                    </div>
                    <button type="submit" className="btn btn-warning btn-sm" disabled={envSaving}>
                      <i className={`fas ${envSaving ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> {envSaving ? 'Saving...' : 'Save .env File'}
                    </button>
                  </form>
                </div>

                <div className="card mt-3" style={{ maxWidth: 1120 }}>
                  <div className="card-title"><i className="fas fa-key"></i> Reset User Password</div>
                  <form onSubmit={(event) => void handleResetUserPassword(event)} autoComplete="off">
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Search User</label>
                        <input className="form-control" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={resetUserSearch} onChange={(event) => setResetUserSearch(event.target.value)} placeholder="Type name or email" />
                      </div>
                      <div className="form-group" style={{ maxWidth: 220 }}>
                        <label className="form-label">Department</label>
                        <select className="form-control" value={resetUserDepartmentFilter} onChange={(event) => setResetUserDepartmentFilter(event.target.value)}>
                          <option value="">All Departments</option>
                          {resetFilterDepartments.map((department) => (
                            <option key={`reset-user-department:${department}`} value={department}>{department}</option>
                          ))}
                        </select>
                      </div>
                      <div className="form-group" style={{ maxWidth: 180 }}>
                        <label className="form-label">Year</label>
                        <select className="form-control" value={resetUserYearFilter} onChange={(event) => setResetUserYearFilter(event.target.value)}>
                          <option value="">All Years</option>
                          {resetFilterYears.map((year) => (
                            <option key={`reset-user-year:${year}`} value={String(year)}>{formatYearLevel(year)}</option>
                          ))}
                        </select>
                      </div>
                    </div>
                    <div className="inline-muted" style={{ marginBottom: 12 }}>
                      Showing {filteredResetUsers.length} account{filteredResetUsers.length === 1 ? '' : 's'}
                    </div>
                    {filteredResetUsers.length ? (
                      <div className="table-wrapper" style={{ maxHeight: 180, marginBottom: 12 }}>
                        <table>
                          <tbody>
                            {filteredResetUsers.map((user) => (
                              <tr key={user.account_email || user.email}>
                                <td>
                                  <strong>{user.name}</strong><br />
                                  <span className="inline-muted">{user.email}</span>
                                </td>
                                <td>{getRoleOptionLabel(user.role, user.designation)}</td>
                                <td style={{ textAlign: 'right' }}>
                                  <button
                                    type="button"
                                    className={`btn btn-sm ${resetPasswordDraft.target_email === (user.account_email || user.email) ? 'btn-primary' : 'btn-outline'}`}
                                    onClick={() => setResetPasswordDraft((prev) => ({ ...prev, target_email: user.account_email || user.email, new_password: '', confirm_password: '' }))}
                                  >
                                    Select
                                  </button>
                                </td>
                              </tr>
                            ))}
                          </tbody>
                        </table>
                      </div>
                    ) : null}
                    {resetPasswordDraft.target_email ? (
                      <div className="detail-display-panel" style={{ marginBottom: 12 }}>
                        <div className="detail-display-grid">
                          <div>
                            <div className="detail-display-label">Selected User</div>
                            <div className="detail-display-value is-strong">
                              {(configData?.resetUsers || []).find((row) => (row.account_email || row.email) === resetPasswordDraft.target_email)?.name || resetPasswordDraft.target_email}
                            </div>
                          </div>
                          <div>
                            <div className="detail-display-label">Scope</div>
                            <div className="detail-display-value">
                              {(() => {
                                const selectedRow = (configData?.resetUsers || []).find((row) => (row.account_email || row.email) === resetPasswordDraft.target_email);
                                if (!selectedRow) return '-';
                                if (selectedRow.role === 'counselor') return `${selectedRow.department || '-'} • ${formatYearLevel(Number(selectedRow.year_level || 1) || 1)}`;
                                return selectedRow.department || getRoleOptionLabel(selectedRow.role, selectedRow.designation);
                              })()}
                            </div>
                          </div>
                        </div>
                      </div>
                    ) : null}
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">New Password</label>
                        <input type="password" className="form-control" autoComplete="new-password" data-lpignore="true" data-1p-ignore="true" minLength={6} required value={resetPasswordDraft.new_password} onChange={(event) => setResetPasswordDraft((prev) => ({ ...prev, new_password: event.target.value }))} />
                      </div>
                      <div className="form-group">
                        <label className="form-label">Confirm Password</label>
                        <input type="password" className="form-control" autoComplete="new-password" data-lpignore="true" data-1p-ignore="true" minLength={6} required value={resetPasswordDraft.confirm_password} onChange={(event) => setResetPasswordDraft((prev) => ({ ...prev, confirm_password: event.target.value }))} />
                      </div>
                    </div>
                    <label className="form-check" style={{ marginBottom: 12 }}>
                      <input type="checkbox" checked={resetPasswordDraft.force_logout} onChange={(event) => setResetPasswordDraft((prev) => ({ ...prev, force_logout: event.target.checked }))} />
                      <span>Force logout from active sessions after reset</span>
                    </label>
                    <button type="submit" className="btn btn-warning" disabled={resetSaving || !resetPasswordDraft.target_email}>
                      <i className={`fas ${resetSaving ? 'fa-spinner fa-spin' : 'fa-key'}`}></i> {resetSaving ? 'Resetting...' : 'Reset Password'}
                    </button>
                  </form>
                </div>

                <div className="card mt-3">
                  <div className="card-title"><i className="fas fa-user-secret"></i> Enter Account Test Mode</div>
                  <div className="form-group">
                    <label className="form-label">Search Account</label>
                    <input className="form-control" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={previewUserSearch} onChange={(event) => setPreviewUserSearch(event.target.value)} placeholder="Type name or email" />
                  </div>
                  {filteredPreviewUsers.length ? (
                    <div className="table-wrapper" style={{ maxHeight: 180, marginBottom: 12 }}>
                      <table>
                        <tbody>
                          {filteredPreviewUsers.map((user) => (
                            <tr key={`preview:${user.account_email || user.email}`}>
                              <td>
                                <strong>{user.name}</strong><br />
                                <span className="inline-muted">{user.email}</span>
                              </td>
                              <td>{getRoleOptionLabel(user.role, user.designation)}</td>
                              <td style={{ textAlign: 'right' }}>
                                <button
                                  type="button"
                                  className={`btn btn-sm ${previewUserEmail === (user.account_email || user.email) ? 'btn-primary' : 'btn-outline'}`}
                                  onClick={() => setPreviewUserEmail(user.account_email || user.email)}
                                >
                                  Select
                                </button>
                              </td>
                            </tr>
                          ))}
                        </tbody>
                      </table>
                    </div>
                  ) : null}
                  {previewShellUser ? (
                    <div className="detail-display-panel" style={{ marginTop: 14 }}>
                      <div className="detail-display-grid">
                        <div>
                          <div className="detail-display-label">Selected Account</div>
                          <div className="detail-display-value is-strong">{previewShellUser.name}</div>
                        </div>
                        <div>
                          <div className="detail-display-label">Role</div>
                          <div className="detail-display-value">{getRoleOptionLabel(previewShellUser.role, previewShellUser.designation)}</div>
                        </div>
                        <div>
                          <div className="detail-display-label">Default Landing Tab</div>
                          <div className="detail-display-value">{getPageTitle(previewDefaultTab, previewShellUser)}</div>
                        </div>
                        <div>
                          <div className="detail-display-label">Allocated Scope</div>
                          <div className="detail-display-value">{previewScopeSummary}</div>
                        </div>
                        <div>
                          <div className="detail-display-label">Email</div>
                          <div className="detail-display-value">{previewShellUser.email}</div>
                        </div>
                        <div>
                          <div className="detail-display-label">Visible Tabs</div>
                          <div className="detail-display-value">
                            {previewTabs.map((tab) => getNavLabel(tab, previewShellUser)).join(', ') || '-'}
                          </div>
                        </div>
                      </div>
                    </div>
                  ) : (
                    <div className="panel-placeholder">Select any user above to review their account details and enter full-page test mode.</div>
                  )}
                  <div className="btn-group" style={{ marginTop: 12 }}>
                    <button type="button" className="btn btn-warning" disabled={!previewUserRecord} onClick={() => previewUserRecord ? void handleStartAccountTestMode(previewUserRecord.account_email || previewUserRecord.email) : undefined}>
                      <i className="fas fa-right-to-bracket"></i> Enter Test Mode
                    </button>
                    {previewUserRecord ? (
                      <button type="button" className="btn btn-outline" onClick={() => setPreviewUserEmail('')}>
                        <i className="fas fa-xmark"></i> Clear
                      </button>
                    ) : null}
                  </div>
                  <div className="ui-preview-note" style={{ marginTop: 12 }}>
                    Test mode opens the full selected account UI using the same navigation and behavior as that user. The sidebar logout action is replaced with a yellow exit button so you can safely return to admin.
                  </div>
                </div>
              </>
            )
          ) : (currentUser.role === 'admin' && activeTab === 'server-console') ? (
            <div className="card mb-3">
              <div className="card-title"><i className="fas fa-stream"></i> Live Server Activity</div>
              <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 10 }}>
                This shows the most recent server log lines captured in memory for quick diagnostics.
              </p>
              <div className="d-flex align-center flex-wrap" style={{ gap: 10, marginBottom: 10 }}>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => void loadServerConsole()}>
                  <i className="fas fa-rotate"></i> Refresh
                </button>
                <span className="text-muted" style={{ fontSize: '.78rem' }}>{serverConsoleData?.meta || 'Showing latest lines'}</span>
              </div>
              <pre
                style={{
                  background: 'rgba(2,6,23,.85)',
                  border: '1px solid var(--border)',
                  borderRadius: 10,
                  padding: 12,
                  maxHeight: 460,
                  overflow: 'auto',
                  color: '#dbeafe',
                  font: "500 .78rem/1.45 'JetBrains Mono','Fira Code','Consolas','Monaco',monospace",
                  whiteSpace: 'pre-wrap',
                  wordBreak: 'break-word',
                  minHeight: 180,
                }}
              >
                {serverConsoleLoading && !serverConsoleData
                  ? 'Loading server console...'
                  : (serverConsoleData?.lines?.length ? serverConsoleData.lines.join('\n') : 'Server console is active. Waiting for log events...')}
              </pre>
            </div>
          ) : ((['admin', 'principal', 'hod', 'deo'].includes(currentUser.role) && activeTab === 'reports') || (currentUser.role === 'counselor' && activeTab === 'test-database')) ? (
            <Suspense fallback={<div className="card"><div className="panel-placeholder">Loading reports workspace...</div></div>}>
              <ReportsTab
                currentUser={currentUser}
                appConfig={bootstrap?.appConfig || null}
                testDetailLoading={testDetailLoading}
                testDetail={testDetail}
                testDetailSearch={testDetailSearch}
                testDetailSort={testDetailSort}
                visibleTestDetailStudents={visibleTestDetailStudents}
                testMetaDraft={testMetaDraft}
                testMetaReadOnly={testMetaReadOnly}
                testMarksReadOnly={testMarksReadOnly}
                savingMeta={savingMeta}
                savingMarks={savingMarks}
                counselorTestsLoading={counselorTestsLoading}
                counselorTestsBySemester={counselorTestsBySemester}
                reportsLoading={reportsLoading}
                reportsData={reportsData}
                reportTestsBySemester={reportTestsBySemester}
                reportUploadDraft={reportUploadDraft}
                reportUploadInputKey={reportUploadInputKey}
                uploadingReport={uploadingReport}
                ScopeBreadcrumb={ScopeBreadcrumb}
                formatYearLevel={formatYearLevel}
                getDefaultBatchNameForYearLevel={getDefaultBatchNameForYearLevel}
                readSummaryMetric={readSummaryMetric}
                onBackFromTestDetail={() => setTestDetail(null)}
                onTestDetailSearchChange={setTestDetailSearch}
                onTestDetailSortChange={setTestDetailSort}
                onSaveAllMarks={() => void handleSaveAllMarks()}
                onTestMetaDraftChange={(field, value) => setTestMetaDraft((prev) => ({ ...prev, [field]: value }))}
                onSaveMetaSubmit={(event) => void handleSaveMeta(event)}
                onUpdateLocalMark={updateLocalMark}
                onSaveRowMarks={(regNo) => void handleSaveRowMarks(regNo)}
                isTestDetailRowDirty={isTestDetailRowDirty}
                onLoadTestDetail={(testId) => void loadTestDetail(testId)}
                onStartCounselorSendFlow={startCounselorSendFlow}
                sendResultOpeningId={sendResultOpeningId}
                onLoadReports={(department, year) => void loadReports(department, year ?? undefined)}
                onUploadReportSubmit={(event) => void handleUploadReport(event)}
                onReportUploadDraftChange={(field, value) => setReportUploadDraft((prev) => ({ ...prev, [field]: value }))}
                onReportUploadFileChange={(file) => setReportUploadDraft((prev) => ({
                  ...prev,
                  file,
                  batch_name: getDefaultBatchNameForYearLevel(reportsData?.selectedYear ?? 1, bootstrap?.appConfig || null),
                  section: '',
                }))}
                onToggleTestBlock={(test) => void handleToggleTestBlock(test)}
                onDeleteTest={(test) => void handleDeleteTest(test)}
              />
            </Suspense>
          ) : (['admin', 'principal'].includes(currentUser.role) && activeTab === 'departments') ? (
            <>
              <div className="card mb-3">
                <div className="card-title"><i className="fas fa-plus"></i> Add Department</div>
                <form onSubmit={(event) => void handleCreateDepartment(event)}>
                  <div className="form-row">
                    <div className="form-group">
                      <label className="form-label">Code</label>
                      <input
                        type="text"
                        className="form-control"
                        value={departmentForm.code}
                        onChange={(event) => setDepartmentForm((prev) => ({ ...prev, code: event.target.value.toUpperCase() }))}
                        required
                        placeholder="CSE"
                      />
                    </div>
                    <div className="form-group">
                      <label className="form-label">Full Name</label>
                      <input
                        type="text"
                        className="form-control"
                        value={departmentForm.name}
                        onChange={(event) => setDepartmentForm((prev) => ({ ...prev, name: event.target.value }))}
                        required
                        placeholder="Computer Science Engineering"
                      />
                    </div>
                  </div>
                  <button type="submit" className="btn btn-primary"><i className="fas fa-plus"></i> Add Department</button>
                </form>
              </div>

              <div className="table-wrapper">
                <table>
                  <thead>
                    <tr>
                      <th>Code</th>
                      <th>Name</th>
                      <th>Status</th>
                      <th>Actions</th>
                    </tr>
                  </thead>
                  <tbody>
                    {departmentsLoading ? (
                      <tr><td colSpan={4} className="text-center text-muted" style={{ padding: 20 }}>Loading departments...</td></tr>
                    ) : departments.length ? departments.map((department) => (
                      <tr key={department.id}>
                        <td><strong>{department.code}</strong></td>
                        <td>{department.name}</td>
                        <td>
                          {department.is_active ? <span className="badge badge-success">Active</span> : <span className="badge badge-muted">Disabled</span>}
                        </td>
                        <td>
                          <div className="btn-group">
                            <button
                              type="button"
                              className="btn btn-outline btn-sm"
                              onClick={() => setDepartmentEdit({ id: department.id, code: department.code, name: department.name })}
                            >
                              <i className="fas fa-pen"></i> Edit
                            </button>
                            <button
                              type="button"
                              className="btn btn-outline btn-sm"
                              onClick={() => handleToggleDepartment(department)}
                            >
                              <i className={`fas fa-${department.is_active ? 'eye-slash' : 'eye'}`}></i> {department.is_active ? 'Disable' : 'Enable'}
                            </button>
                            <button
                              type="button"
                              className="btn btn-danger btn-sm"
                              onClick={() => handleDeleteDepartment(department)}
                            >
                              <i className="fas fa-trash"></i>
                            </button>
                          </div>
                        </td>
                      </tr>
                    )) : (
                      <tr><td colSpan={4} className="text-center text-muted" style={{ padding: 20 }}>No departments found.</td></tr>
                    )}
                  </tbody>
                </table>
              </div>
            </>
          ) : (
            <div className="card">
              <div className="card-title"><i className="fas fa-screwdriver-wrench"></i> Migration Surface</div>
              <div className="panel-placeholder">
                This tab is part of the React + Hono rebuild foundation. The shared Shine shell, auth/session model,
                theme system, role navigation, and initial admin data flow are now running on the new stack. The remaining
                module for <strong>{getPageTitle(activeTab, currentUser)}</strong> is still to be ported with full UI parity.
              </div>
            </div>
          )}
        </div>

        {embeddedWhatsappSidepaneLayoutActive ? null : (
          <footer className="global-footer">
            <div className="global-footer-inner">
              <div className="global-footer-left">
                <img src="/assets/banner.png" alt="RMKCET Banner" className="global-footer-banner-image" loading="lazy" />
                <span className="global-footer-text">Department of Science and Humanities</span>
              </div>
              <div className="global-footer-links">
                {canOpenFooterTemplates ? (
                  <button
                    type="button"
                    className="global-footer-link global-footer-btn"
                    onClick={() => setTemplateDownloadsOpen(true)}
                  >
                    Templates
                  </button>
                ) : null}
                {currentUser.role === 'counselor' ? (
                  <a
                    className="global-footer-link global-footer-btn"
                    href="https://apps.microsoft.com/detail/9NKSQGP7F2NH?hl=en-us&gl=IN&ocid=pdpshare"
                    target="_blank"
                    rel="noopener noreferrer"
                  >
                    WhatsApp Download
                  </a>
                ) : null}
                {!runtimeConfig.isDesktop ? (
                  <a className="global-footer-link global-footer-btn" href="/api/desktop/installer/exe">
                    Windows App
                  </a>
                ) : null}
                <a className="global-footer-link global-footer-btn" href="/api/footer/credits">Credits</a>
                {currentUser.role !== 'admin' ? (
                  <a className="global-footer-link global-footer-btn" href={getFooterSupportHref(currentUser)} target="_blank" rel="noreferrer">Support</a>
                ) : null}
              </div>
            </div>
          </footer>
        )}
      </main>

      {templateDownloadsOpen ? (
        <div className="modal-overlay open" onClick={() => setTemplateDownloadsOpen(false)}>
          <div className="modal template-download-modal" onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-circle-info"></i> Templates</h3>
              <button className="modal-close" type="button" onClick={() => setTemplateDownloadsOpen(false)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p className="template-download-copy">
              Download the standard Shine Excel templates from the rebuild assets.
            </p>
            <div className="template-download-list">
              {RESOURCE_TEMPLATES.map((template) => (
                <a key={template.key} className="btn btn-outline template-download-link" href={template.href} download>
                  <i className="fas fa-file-arrow-down"></i> Download {template.fileName}
                </a>
              ))}
            </div>
          </div>
        </div>
      ) : null}

      {databaseProgress ? (
        <div className="modal-overlay open">
          <div className="modal" style={{ maxWidth: 420 }}>
            <div className="modal-header">
              <h3><i className="fas fa-database"></i> {databaseProgress.title}</h3>
            </div>
            <div style={{ padding: '4px 2px 10px' }}>
              <div className="d-flex align-center" style={{ gap: 12, marginBottom: 14 }}>
                <div className="spinner-ring" aria-hidden="true"></div>
                <p style={{ margin: 0, color: 'var(--text-dim)', lineHeight: 1.6 }}>{databaseProgress.body}</p>
              </div>
              <div className="inline-muted">The page will refresh automatically when the operation finishes.</div>
            </div>
          </div>
        </div>
      ) : null}

      {selectedNoticeCompletion ? (
        <div className="modal-overlay open" onClick={() => setSelectedNoticeCompletion(null)}>
          <div className="modal notice-detail-modal" onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-circle-info"></i> Counselor Notice Details</h3>
              <button className="modal-close" type="button" onClick={() => setSelectedNoticeCompletion(null)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <div className="detail-display-panel">
              <div className="detail-display-grid">
                <div className="detail-display-card">
                  <label className="form-label">Name</label>
                  <div className="detail-display-value is-strong">{selectedNoticeCompletion.name}</div>
                </div>
                <div className="detail-display-card">
                  <label className="form-label">Email</label>
                  <div className="detail-display-value">{selectedNoticeCompletion.email}</div>
                </div>
                <div className="detail-display-card">
                  <label className="form-label">Department</label>
                  <div className="detail-display-value is-strong">{selectedNoticeCompletion.department}</div>
                </div>
                <div className="detail-display-card">
                  <label className="form-label">Year</label>
                  <div className="detail-display-value is-strong">{formatYearLevel(selectedNoticeCompletion.year_level || 1)}</div>
                </div>
                <div className="detail-display-card">
                  <label className="form-label">No. of Students</label>
                  <div className="detail-display-metric">{selectedNoticeCompletion.student_count}</div>
                </div>
                <div className="detail-display-card">
                  <label className="form-label">No. of Messages Sent</label>
                  <div className="detail-display-metric">{selectedNoticeCompletion.message_count}</div>
                </div>
              </div>
              <div className="detail-display-card">
                <label className="form-label">Pending Notices</label>
                <div className="detail-display-meta" style={{ marginBottom: 10 }}>
                  {selectedNoticeCompletion.pending_notice_count || 0} pending notice{selectedNoticeCompletion.pending_notice_count === 1 ? '' : 's'}
                </div>
                <div className="detail-display-list">
                  {(selectedNoticeCompletion.pending_notice_titles || []).length ? (
                    selectedNoticeCompletion.pending_notice_titles.map((title) => (
                      <div key={title} className="detail-display-pill">{`> ${title}`}</div>
                    ))
                  ) : (
                    <div className="detail-display-pill">No pending notices.</div>
                  )}
                </div>
              </div>
              <div className="btn-group" style={{ justifyContent: 'flex-end', marginTop: 8 }}>
                <button type="button" className="btn btn-primary btn-sm" onClick={() => setSelectedNoticeCompletion(null)}>Close</button>
              </div>
            </div>
          </div>
        </div>
      ) : null}

      {desktopSettingsPanelOpen && runtimeConfig.isDesktop ? (
        <div className="modal-overlay open" onClick={() => setDesktopSettingsPanelOpen(false)}>
          <div className="modal" style={{ maxWidth: 980 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-desktop"></i> Desktop App</h3>
              <button className="modal-close" type="button" onClick={() => setDesktopSettingsPanelOpen(false)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            {renderDesktopAppSettingsPanel()}
          </div>
        </div>
      ) : null}

      {loginNotificationPrompt ? (
        <div className="modal-overlay open" onClick={() => setLoginNotificationPrompt(null)}>
          <div className="modal" style={{ maxWidth: 520 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-circle-exclamation"></i> Notification</h3>
            </div>
            <div className="notification-login-body">
              <strong>{loginNotificationPrompt.title}</strong>
              <p>{loginNotificationPrompt.body}</p>
            </div>
            <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => {
                markNotificationsRead([loginNotificationPrompt.key]);
                setLoginNotificationPrompt(null);
                openNotificationCenter();
              }}>
                Check Notification Center
              </button>
              <button type="button" className="btn btn-primary btn-sm" onClick={() => {
                markNotificationsRead([loginNotificationPrompt.key]);
                setLoginNotificationPrompt(null);
              }}>
                OK
              </button>
            </div>
          </div>
        </div>
      ) : null}

      {forgotPasswordState.open ? (
        <div
          className="modal-overlay open"
          onClick={() => {
            if (forgotPasswordState.loading) return;
            setForgotPasswordState({
              open: false,
              stage: 'request',
              identifier: '',
              maskedEmail: '',
              otp_code: '',
              new_password: '',
              confirm_password: '',
              loading: false,
              error: '',
            });
          }}
        >
          <div className="modal" style={{ maxWidth: 480 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-key"></i> Forgot Password</h3>
              <button
                className="modal-close"
                type="button"
                onClick={() => setForgotPasswordState({
                  open: false,
                  stage: 'request',
                  identifier: '',
                  maskedEmail: '',
                  otp_code: '',
                  new_password: '',
                  confirm_password: '',
                  loading: false,
                  error: '',
                })}
                disabled={forgotPasswordState.loading}
              >
                <i className="fas fa-xmark"></i>
              </button>
            </div>

            {forgotPasswordState.stage === 'request' ? (
              <form onSubmit={(event) => void handleForgotPasswordRequest(event)} autoComplete="off">
                <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 14 }}>
                  Enter your email or full name. We&apos;ll send a password reset OTP to your registered email address.
                </p>
                <div className="form-group">
                  <label className="form-label">Email or Name</label>
                  <input
                    className="form-control"
                    autoComplete="off"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.identifier}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, identifier: event.target.value }))}
                    placeholder="Enter your email or full name"
                    required
                    autoFocus
                  />
                </div>
                {forgotPasswordState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{forgotPasswordState.error}</span>
                  </div>
                ) : null}
                <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => setForgotPasswordState({
                      open: false,
                      stage: 'request',
                      identifier: '',
                      maskedEmail: '',
                      otp_code: '',
                      new_password: '',
                      confirm_password: '',
                      loading: false,
                      error: '',
                    })}
                    disabled={forgotPasswordState.loading}
                  >
                    Cancel
                  </button>
                  <button type="submit" className="btn btn-primary btn-sm" disabled={forgotPasswordState.loading}>
                    <i className={`fas ${forgotPasswordState.loading ? 'fa-spinner fa-spin' : 'fa-paper-plane'}`}></i>
                    {forgotPasswordState.loading ? 'Sending...' : 'Send OTP'}
                  </button>
                </div>
              </form>
            ) : null}

            {forgotPasswordState.stage === 'verify' ? (
              <form onSubmit={(event) => void handleForgotPasswordVerify(event)} autoComplete="off">
                <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 14 }}>
                  OTP sent to {forgotPasswordState.maskedEmail || 'your email'}.
                </p>
                <div className="form-group">
                  <label className="form-label">Reset OTP</label>
                  <input
                    className="form-control otp-code-input"
                    autoComplete="off"
                    inputMode="numeric"
                    pattern="\d{6}"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.otp_code}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, otp_code: normalizeOtpCode(event.target.value) }))}
                    placeholder="Enter 6-digit OTP"
                    minLength={6}
                    maxLength={6}
                    required
                    autoFocus
                  />
                </div>
                {forgotPasswordState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{forgotPasswordState.error}</span>
                  </div>
                ) : null}
                <div className="btn-group" style={{ justifyContent: 'space-between' }}>
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => setForgotPasswordState((prev) => ({
                      ...prev,
                      stage: 'request',
                      otp_code: '',
                      error: '',
                      loading: false,
                    }))}
                    disabled={forgotPasswordState.loading}
                  >
                    <i className="fas fa-arrow-left"></i> Back
                  </button>
                  <button type="submit" className="btn btn-primary btn-sm" disabled={forgotPasswordState.loading}>
                    <i className={`fas ${forgotPasswordState.loading ? 'fa-spinner fa-spin' : 'fa-shield-halved'}`}></i>
                    {forgotPasswordState.loading ? 'Verifying...' : 'Verify OTP'}
                  </button>
                </div>
              </form>
            ) : null}

            {forgotPasswordState.stage === 'reset' ? (
              <form onSubmit={(event) => void handleForgotPasswordComplete(event)} autoComplete="off">
                <p style={{ fontSize: '.84rem', color: 'var(--text-dim)', marginBottom: 14 }}>
                  Set a new password for {forgotPasswordState.maskedEmail || 'your account'}.
                </p>
                <div className="form-group">
                  <label className="form-label">New Password</label>
                  <input
                    className="form-control"
                    type="password"
                    autoComplete="new-password"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.new_password}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, new_password: event.target.value }))}
                    placeholder="Enter new password"
                    required
                    autoFocus
                  />
                </div>
                <div className="form-group">
                  <label className="form-label">Confirm Password</label>
                  <input
                    className="form-control"
                    type="password"
                    autoComplete="new-password"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.confirm_password}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, confirm_password: event.target.value }))}
                    placeholder="Re-enter new password"
                    required
                  />
                </div>
                {forgotPasswordState.error ? (
                  <div className="flash flash-error" style={{ marginBottom: 14 }}>
                    <i className="fas fa-times-circle"></i>
                    <span>{forgotPasswordState.error}</span>
                  </div>
                ) : null}
                <div className="btn-group" style={{ justifyContent: 'space-between' }}>
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => setForgotPasswordState((prev) => ({
                      ...prev,
                      stage: 'verify',
                      new_password: '',
                      confirm_password: '',
                      error: '',
                      loading: false,
                    }))}
                    disabled={forgotPasswordState.loading}
                  >
                    <i className="fas fa-arrow-left"></i> Back
                  </button>
                  <button type="submit" className="btn btn-primary btn-sm" disabled={forgotPasswordState.loading}>
                    <i className={`fas ${forgotPasswordState.loading ? 'fa-spinner fa-spin' : 'fa-key'}`}></i>
                    {forgotPasswordState.loading ? 'Updating...' : 'Reset Password'}
                  </button>
                </div>
              </form>
            ) : null}
          </div>
        </div>
      ) : null}

      {selfPasswordModalOpen && currentUser ? (
        <div
          className="modal-overlay open"
          onClick={() => {
            if (selfPasswordSaving || selfPasswordSendingOtp) return;
            setSelfPasswordModalOpen(false);
            setSelfPasswordDraft({
              current_password: '',
              otp_code: '',
              new_password: '',
              confirm_password: '',
            });
            setSelfPasswordOtpSentTo('');
          }}
        >
          <div className="modal" style={{ maxWidth: 500 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-key"></i> Change Password</h3>
              <button
                className="modal-close"
                type="button"
                onClick={() => {
                  setSelfPasswordModalOpen(false);
                  setSelfPasswordDraft({
                    current_password: '',
                    otp_code: '',
                    new_password: '',
                    confirm_password: '',
                  });
                  setSelfPasswordOtpSentTo('');
                }}
                disabled={selfPasswordSaving || selfPasswordSendingOtp}
              >
                <i className="fas fa-xmark"></i>
              </button>
            </div>

            {bootstrap?.authUi?.selfPasswordOtpEnabled ? (
              <>
                <button
                  type="button"
                  className="btn btn-outline"
                  style={{ width: '100%', justifyContent: 'center', marginBottom: 12 }}
                  onClick={() => void handleSendSelfPasswordOtp()}
                  disabled={selfPasswordSendingOtp || selfPasswordSaving}
                >
                  <i className={`fas ${selfPasswordSendingOtp ? 'fa-spinner fa-spin' : 'fa-paper-plane'}`}></i>
                  {selfPasswordSendingOtp ? 'Sending OTP...' : 'Send OTP To My Email'}
                </button>
                <p style={{ fontSize: '.78rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                  OTP verification is enabled for password reset. Enter the OTP from your mailbox before saving the new password.
                  {selfPasswordOtpSentTo ? ` OTP sent to ${selfPasswordOtpSentTo}.` : ''}
                </p>
              </>
            ) : bootstrap?.authUi?.adminCurrentPasswordFallbackEnabled ? (
              <p style={{ fontSize: '.78rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                Confirm your current password before saving the new password.
              </p>
            ) : (
              <p style={{ fontSize: '.78rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                Set a new password for your account below.
              </p>
            )}

            <form onSubmit={(event) => void handleUpdateSelfPassword(event)} autoComplete="off">
              {bootstrap?.authUi?.adminCurrentPasswordFallbackEnabled ? (
                <div className="form-group">
                  <label className="form-label">Current Password</label>
                  <input
                    className="form-control"
                    type="password"
                    autoComplete="current-password"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={selfPasswordDraft.current_password}
                    onChange={(event) => setSelfPasswordDraft((prev) => ({ ...prev, current_password: event.target.value }))}
                    placeholder="Enter current password"
                    required
                  />
                </div>
              ) : null}

              {bootstrap?.authUi?.selfPasswordOtpEnabled ? (
                <div className="form-group">
                  <label className="form-label">OTP Code</label>
                  <input
                    className="form-control otp-code-input"
                    autoComplete="off"
                    inputMode="numeric"
                    pattern="\d{6}"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={selfPasswordDraft.otp_code}
                    onChange={(event) => setSelfPasswordDraft((prev) => ({ ...prev, otp_code: normalizeOtpCode(event.target.value) }))}
                    placeholder="Enter 6-digit OTP"
                    minLength={6}
                    maxLength={6}
                    required
                  />
                </div>
              ) : null}

              <div className="form-group">
                <label className="form-label">New Password</label>
                <input
                  className="form-control"
                  type="password"
                  autoComplete="new-password"
                  data-lpignore="true"
                  data-1p-ignore="true"
                  value={selfPasswordDraft.new_password}
                  onChange={(event) => setSelfPasswordDraft((prev) => ({ ...prev, new_password: event.target.value }))}
                  placeholder="Enter new password"
                  required
                />
              </div>

              <div className="form-group">
                <label className="form-label">Confirm Password</label>
                <input
                  className="form-control"
                  type="password"
                  autoComplete="new-password"
                  data-lpignore="true"
                  data-1p-ignore="true"
                  value={selfPasswordDraft.confirm_password}
                  onChange={(event) => setSelfPasswordDraft((prev) => ({ ...prev, confirm_password: event.target.value }))}
                  placeholder="Re-enter new password"
                  required
                />
              </div>

              <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                <button
                  type="button"
                  className="btn btn-outline btn-sm"
                  onClick={() => {
                    setSelfPasswordModalOpen(false);
                    setSelfPasswordDraft({
                      current_password: '',
                      otp_code: '',
                      new_password: '',
                      confirm_password: '',
                    });
                    setSelfPasswordOtpSentTo('');
                  }}
                  disabled={selfPasswordSaving || selfPasswordSendingOtp}
                >
                  Cancel
                </button>
                <button type="submit" className="btn btn-primary btn-sm" disabled={selfPasswordSaving || selfPasswordSendingOtp}>
                  <i className={`fas ${selfPasswordSaving ? 'fa-spinner fa-spin' : 'fa-save'}`}></i>
                  {selfPasswordSaving ? 'Saving...' : 'Update Password'}
                </button>
              </div>
            </form>
          </div>
        </div>
      ) : null}

      {userEditDraft ? (
        <div className="modal-overlay open" onClick={() => setUserEditDraft(null)}>
          <div className="modal" style={{ maxWidth: 720 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-edit"></i> Edit User</h3>
              <button className="modal-close" type="button" onClick={() => setUserEditDraft(null)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <form onSubmit={(event) => void handleSaveUserEdit(event)} autoComplete="off">
              <div className="form-row">
                <div className="form-group">
                  <label className="form-label">Full Name</label>
                  <input className="form-control" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={userEditDraft.name} onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, name: event.target.value } : prev)} required />
                </div>
                <div className="form-group">
                  <label className="form-label">Email</label>
                  <input className="form-control" type="email" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={userEditDraft.email} onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, email: event.target.value } : prev)} required />
                </div>
              </div>
              <div className="form-row">
                <div className="form-group">
                  <label className="form-label">New Password</label>
                  <input className="form-control" type="password" autoComplete="new-password" data-lpignore="true" data-1p-ignore="true" value={userEditDraft.password} onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, password: event.target.value } : prev)} placeholder="Leave blank to keep current password" />
                </div>
                {currentUser.role === 'admin' ? (
                  <div className="form-group">
                    <label className="form-label">Role</label>
                    <select className="form-control" value={userEditDraft.role} onChange={(event) => setUserEditDraft((prev) => prev ? {
                      ...prev,
                      role: event.target.value as Role,
                      designation: event.target.value === 'principal' ? (String(prev.designation || '').trim() || 'Higher Official') : '',
                      scope_pairs: [],
                      department: '',
                      year_level: '1',
                    } : prev)}>
                      {userAssignableRoles.map((role) => (
                        <option key={role} value={role}>{getRoleOptionLabel(role)}</option>
                      ))}
                    </select>
                  </div>
                ) : null}
              </div>
              {userEditDraft.role === 'principal' ? (
                <div className="form-row">
                  <div className="form-group">
                    <label className="form-label">Higher Official Designation</label>
                    <input
                      className="form-control"
                      autoComplete="off"
                      value={userEditDraft.designation}
                      onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, designation: event.target.value } : prev)}
                      placeholder="Vice Chairman, Dean, Director..."
                    />
                  </div>
                </div>
              ) : null}
              {(userEditDraft.role === 'hod' || userEditDraft.role === 'deo') ? (
                <div className="card mb-2" style={{ padding: 12, background: 'rgba(59,130,246,.08)', border: '1px solid rgba(59,130,246,.28)' }}>
                  <div className="card-title" style={{ fontSize: '.86rem', marginBottom: 10 }}><i className="fas fa-layer-group"></i> Assigned Scopes</div>
                  <div className="scope-grid">
                    {userSelectableDepartments.map((department) => (
                      <div key={department.id} className="scope-item">
                        <div className="scope-item-title">{department.code}</div>
                        <div className="scope-year-list">
                          {(currentUser.role === 'admin' ? [1, 2, 3, 4] : userScopeOptions.filter((scope) => scope.department === department.code).map((scope) => scope.year_level)).map((year) => {
                            const value = `${department.code}::${year}`;
                            return (
                              <label key={value} className="scope-chip">
                                <input
                                  type="checkbox"
                                  checked={userEditDraft.scope_pairs.includes(value)}
                                  onChange={(event) => setUserEditDraft((prev) => prev ? {
                                    ...prev,
                                    scope_pairs: event.target.checked ? [...prev.scope_pairs, value] : prev.scope_pairs.filter((item) => item !== value),
                                  } : prev)}
                                />
                                <span>Y{year}</span>
                              </label>
                            );
                          })}
                        </div>
                      </div>
                    ))}
                  </div>
                </div>
              ) : null}
              {userEditDraft.role === 'counselor' ? (
                <>
                  <div className="form-row">
                    <div className="form-group">
                      <label className="form-label">Department</label>
                      <select className="form-control" value={userEditDraft.department} onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, department: event.target.value } : prev)}>
                        <option value="">-- Select --</option>
                        {userSelectableDepartments.map((department) => (
                          <option key={department.id} value={department.code}>{department.code} - {department.name}</option>
                        ))}
                      </select>
                    </div>
                    <div className="form-group">
                      <label className="form-label">Year</label>
                      <select className="form-control" value={userEditDraft.year_level} onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, year_level: event.target.value } : prev)}>
                        {[1, 2, 3, 4].map((year) => (
                          <option key={year} value={year}>{formatYearLevel(year)}</option>
                        ))}
                      </select>
                    </div>
                  </div>
                  <div className="form-group" style={{ maxWidth: 220 }}>
                    <label className="form-label">Max Students</label>
                    <input className="form-control" type="number" min="1" max="500" value={userEditDraft.max_students} onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, max_students: event.target.value } : prev)} />
                  </div>
                  <div className="card mt-3 mb-2" style={{ padding: 14, background: 'rgba(34,197,94,.08)', border: '1px solid rgba(34,197,94,.30)' }}>
                    <div className="d-flex justify-between align-center mb-3" style={{ gap: 12 }}>
                      <label className="form-label" style={{ margin: 0 }}><i className="fas fa-users"></i> Student Management</label>
                      <span className="badge badge-success">{typeof users.find((item) => (item.account_email || item.email) === userEditDraft.original_email)?.student_count === 'number' ? users.find((item) => (item.account_email || item.email) === userEditDraft.original_email)?.student_count : 0} students</span>
                    </div>
                    <div className="btn-group">
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => {
                        const targetUser = users.find((item) => (item.account_email || item.email) === userEditDraft.original_email);
                        if (targetUser) void loadCounselorStudents(targetUser);
                      }}>
                        <i className="fas fa-pen"></i> Edit/View All
                      </button>
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => {
                        const targetUser = users.find((item) => (item.account_email || item.email) === userEditDraft.original_email);
                        if (targetUser) void loadCounselorStudents(targetUser);
                      }}>
                        <i className="fas fa-upload"></i> Upload Excel
                      </button>
                    </div>
                  </div>
                </>
              ) : null}
              <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => setUserEditDraft(null)}>Cancel</button>
                <button type="submit" className="btn btn-primary btn-sm" disabled={userSaving}>
                  <i className={`fas ${userSaving ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> Save Changes
                </button>
              </div>
            </form>
          </div>
        </div>
      ) : null}

      {userActionTarget ? (
        <div className="modal-overlay open" onClick={() => { if (!userActionLoading) setUserActionTarget(null); }}>
          <div className="modal" style={{ maxWidth: 460 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3>
                <i className={`fas ${userActionTarget.kind === 'delete' ? 'fa-trash' : 'fa-triangle-exclamation'}`}></i>{' '}
                {userActionTarget.kind === 'delete'
                  ? 'Delete User'
                  : userActionTarget.kind === 'lock'
                    ? 'Lock User'
                    : 'Unlock User'}
              </h3>
              <button className="modal-close" type="button" onClick={() => setUserActionTarget(null)} disabled={userActionLoading}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>
              {userActionTarget.kind === 'delete'
                ? `Delete ${userActionTarget.user.name}? This cannot be undone.`
                : userActionTarget.kind === 'lock'
                  ? `Lock ${userActionTarget.user.name}? This logs the user out from active sessions.`
                  : `Unlock ${userActionTarget.user.name} and restore account access?`}
            </p>
            <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => setUserActionTarget(null)} disabled={userActionLoading}>Cancel</button>
              <button
                type="button"
                className={`btn btn-sm ${userActionTarget.kind === 'delete' ? 'btn-danger' : userActionTarget.kind === 'lock' ? 'btn-warning' : 'btn-success'}`}
                onClick={() => void handleConfirmUserAction()}
                disabled={userActionLoading}
              >
                <i className={`fas ${userActionLoading ? 'fa-spinner fa-spin' : userActionTarget.kind === 'delete' ? 'fa-trash' : userActionTarget.kind === 'lock' ? 'fa-lock' : 'fa-unlock'}`}></i>
                {userActionLoading ? 'Working...' : userActionTarget.kind === 'delete' ? 'Delete' : userActionTarget.kind === 'lock' ? 'Lock' : 'Unlock'}
              </button>
            </div>
          </div>
        </div>
      ) : null}

      {linkedUserGroupEmail && linkedUserGroupRecords.length ? (
        <div className="modal-overlay open" onClick={() => setLinkedUserGroupEmail('')}>
          <div className="modal" style={{ maxWidth: 760 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-layer-group"></i> Manage Roles</h3>
              <button className="modal-close" type="button" onClick={() => setLinkedUserGroupEmail('')}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>
              {linkedUserGroupEmail}
            </p>
            <div className="table-wrapper">
              <table>
                <thead>
                  <tr>
                    <th>Role</th>
                    <th>Department</th>
                    <th>Year</th>
                    <th>Status</th>
                    <th>Actions</th>
                  </tr>
                </thead>
                <tbody>
                  {linkedUserGroupRecords.map((user) => (
                    <tr key={user.account_email || `${user.email}:${user.role}`}>
                      <td><span className={`badge ${getRoleBadgeClass(user.role)}`}>{getRoleOptionLabel(user.role, user.designation)}</span></td>
                      <td>{user.role === 'hod' || user.role === 'deo' ? ((user.scopes || []).map((scope) => scope.department).slice(0, 2).join(', ') || user.department || '-') : (user.department || '-')}</td>
                      <td>{user.role === 'counselor' ? formatYearLevel(user.year_level || 1) : '-'}</td>
                      <td><span className={`badge ${user.is_active && !user.is_locked ? 'badge-success' : 'badge-danger'}`}>{user.is_active && !user.is_locked ? 'Active' : 'Inactive'}</span></td>
                      <td>
                        <div className="btn-group">
                          {user.can_edit ? (
                            <button type="button" className="btn btn-outline btn-sm" onClick={() => { setLinkedUserGroupEmail(''); openEditUserModal(user); }}>
                              <i className="fas fa-edit"></i> Edit
                            </button>
                          ) : null}
                          {user.can_manage ? (
                            <>
                              <button
                                type="button"
                                className={`btn btn-sm ${user.is_locked ? 'btn-success' : 'btn-warning'}`}
                                onClick={() => {
                                  setLinkedUserGroupEmail('');
                                  setUserActionTarget({ kind: user.is_locked ? 'unlock' : 'lock', user });
                                }}
                              >
                                <i className={`fas fa-${user.is_locked ? 'unlock' : 'lock'}`}></i>
                              </button>
                              <button
                                type="button"
                                className="btn btn-danger btn-sm"
                                onClick={() => {
                                  setLinkedUserGroupEmail('');
                                  setUserActionTarget({ kind: 'delete', user });
                                }}
                              >
                                <i className="fas fa-trash"></i>
                              </button>
                            </>
                          ) : (
                            <span className="badge badge-info">View Only</span>
                          )}
                        </div>
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
          </div>
        </div>
      ) : null}

      {studentListModalOpen && studentListCounselor ? (
        <div className="modal-overlay open" onClick={() => { if (!studentListSaving) setStudentListModalOpen(false); }}>
          <div className="modal" style={{ maxWidth: 980, maxHeight: '90vh', overflow: 'auto' }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-user-pen"></i> Manage Students - {studentListCounselor.name}</h3>
              <button className="modal-close" type="button" onClick={() => setStudentListModalOpen(false)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <div className="d-flex justify-between align-center mb-2" style={{ gap: 10 }}>
              <p style={{ fontSize: '.82rem', color: 'var(--text-dim)', margin: 0 }}>Manage individual students or replace the full list using Excel.</p>
              <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteAllStudents()} disabled={studentListSaving}>
                <i className="fas fa-trash"></i> Delete Entire Student List
              </button>
            </div>
            <div className="card mb-2" style={{ padding: 14 }}>
              <div className="card-title" style={{ fontSize: '.9rem' }}><i className="fas fa-upload"></i> Upload Student Excel</div>
              <div className="file-input-wrapper">
                <i className="fas fa-file-excel"></i>
                <div className="file-text">Choose file</div>
                <input
                  key={studentUploadKey}
                  type="file"
                  accept=".xlsx,.xls"
                  onChange={(event) => void handleUploadStudentsForCounselor(event.target.files?.[0] || null)}
                />
              </div>
              <p style={{ fontSize: '.8rem', color: 'var(--text-dim)', margin: '12px 0 0 0' }}>Excel should contain columns like `RNO`, `NAME`, and `WNO`.</p>
            </div>
            <div className="card mb-2" style={{ padding: 14 }}>
              <div className="card-title" style={{ fontSize: '.9rem' }}><i className="fas fa-user-plus"></i> Add Student Manually</div>
              <form onSubmit={(event) => void handleSaveStudentRow(event)} autoComplete="off">
                <div className="form-row">
                  <div className="form-group"><label className="form-label">Reg No</label><input className="form-control" autoComplete="off" value={studentQuickAdd.reg_no} onChange={(event) => setStudentQuickAdd((prev) => ({ ...prev, reg_no: event.target.value }))} required /></div>
                  <div className="form-group"><label className="form-label">Student Name</label><input className="form-control" autoComplete="off" value={studentQuickAdd.student_name} onChange={(event) => setStudentQuickAdd((prev) => ({ ...prev, student_name: event.target.value }))} required /></div>
                  <div className="form-group"><label className="form-label">WhatsApp No</label><input className="form-control" autoComplete="off" value={studentQuickAdd.parent_phone} onChange={(event) => setStudentQuickAdd((prev) => ({ ...prev, parent_phone: event.target.value }))} /></div>
                  <div className="form-group"><label className="form-label">Parent Email</label><input className="form-control" type="email" autoComplete="off" value={studentQuickAdd.parent_email} onChange={(event) => setStudentQuickAdd((prev) => ({ ...prev, parent_email: event.target.value }))} /></div>
                </div>
                <button className="btn btn-primary btn-sm" type="submit" disabled={studentListSaving}><i className="fas fa-plus"></i> Add Student</button>
              </form>
            </div>
            <div className="table-wrapper">
              <table>
                <thead>
                  <tr>
                    <th>Reg No</th>
                    <th>Name</th>
                    <th>WhatsApp No</th>
                    <th>Parent Email</th>
                    <th>Actions</th>
                  </tr>
                </thead>
                <tbody>
                  {studentListLoading ? (
                    <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 24 }}>Loading students...</td></tr>
                  ) : studentListRows.length ? studentListRows.map((student) => (
                    <tr key={student.reg_no}>
                      <td>{student.reg_no}</td>
                      <td>{student.student_name}</td>
                      <td>{student.parent_phone || '-'}</td>
                      <td>{student.parent_email || '-'}</td>
                      <td>
                        <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteStudentRow(student.reg_no)} disabled={studentListSaving}>
                          <i className="fas fa-trash"></i>
                        </button>
                      </td>
                    </tr>
                  )) : (
                    <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 24 }}>No students assigned yet.</td></tr>
                  )}
                </tbody>
              </table>
            </div>
          </div>
        </div>
      ) : null}

      {roleSwitchModalOpen && currentUser ? (
        <div className="modal-overlay open" onClick={() => !roleSwitchLoading && setRoleSwitchModalOpen(false)}>
          <div className="modal" style={{ maxWidth: 560 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-repeat"></i> Change Role</h3>
              <button className="modal-close" type="button" onClick={() => !roleSwitchLoading && setRoleSwitchModalOpen(false)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <form onSubmit={(event) => void handleSwitchRole(event)}>
              <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>
                This login is linked to multiple SHINE roles for <strong>{roleSwitchLoginDisplayEmail || normalizeSharedRoleDisplayEmail(currentUser.email)}</strong>. Choose the workspace you want to open next.
              </p>
              <div style={{ display: 'grid', gap: 8 }}>
                {orderedRoleSwitchOptions.map((option) => {
                  const isCurrentOption = isCurrentRoleSwitchOption(option, currentUser);
                  return (
                  <label
                    key={option.accountEmail}
                    className="scope-chip"
                    style={{
                      display: 'flex',
                      alignItems: 'center',
                      gap: 10,
                      padding: '12px 14px',
                      borderRadius: 12,
                      border: option.accountEmail === roleSwitchSelectedAccountEmail ? '1px solid var(--primary)' : '1px solid var(--border)',
                      background: option.accountEmail === roleSwitchSelectedAccountEmail ? 'rgba(102,126,234,.12)' : 'var(--bg-input)',
                    }}
                  >
                    <input
                      type="radio"
                      name="session-role-selection"
                      checked={option.accountEmail === roleSwitchSelectedAccountEmail}
                      onChange={() => setRoleSwitchSelectedAccountEmail(option.accountEmail)}
                    />
                    <span style={{ display: 'grid', gap: 3 }}>
                      <strong>
                        {getRoleOptionLabel(option.role, option.designation)}
                        {isCurrentOption ? ' (Current)' : ''}
                      </strong>
                      <span className="inline-muted">
                        {option.name}
                        {option.department ? ` - ${option.department}` : ''}
                        {option.role === 'counselor' ? ` - ${formatYearLevel(option.year_level || 1)}` : ''}
                      </span>
                    </span>
                  </label>
                )})}
              </div>
              {roleSwitchError ? (
                <div className="flash flash-error" style={{ marginTop: 14 }}>
                  <i className="fas fa-times-circle"></i>
                  <span>{roleSwitchError}</span>
                </div>
              ) : null}
              <div className="btn-group" style={{ justifyContent: 'flex-end', marginTop: 16 }}>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => setRoleSwitchModalOpen(false)} disabled={roleSwitchLoading}>
                  Cancel
                </button>
                <button type="submit" className="btn btn-primary btn-sm" disabled={roleSwitchLoading}>
                  <i className={`fas ${roleSwitchLoading ? 'fa-spinner fa-spin' : 'fa-right-left'}`}></i> {roleSwitchLoading ? 'Switching...' : 'Switch Role'}
                </button>
              </div>
            </form>
          </div>
        </div>
      ) : null}

      {missingWhatsappPrompt ? (
        <div className="modal-overlay open" onClick={() => setMissingWhatsappPrompt(null)}>
          <div className="modal" style={{ maxWidth: 480 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fab fa-whatsapp"></i> WhatsApp App Missing</h3>
              <button className="modal-close" type="button" onClick={() => setMissingWhatsappPrompt(null)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>
              WhatsApp Desktop is not installed on this device. Install it from Microsoft Store, or continue with WhatsApp Web mode for <strong>{missingWhatsappPrompt.title}</strong>.
            </p>
            <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => setMissingWhatsappPrompt(null)}>
                Back
              </button>
              <button type="button" className="btn btn-primary btn-sm" onClick={() => installWhatsappFromPrompt()}>
                <i className="fas fa-download"></i> Install From Store
              </button>
              <button type="button" className="btn btn-success btn-sm" onClick={() => useWhatsappWebFromPrompt()}>
                <i className="fas fa-globe"></i> Use Web Mode
              </button>
            </div>
          </div>
        </div>
      ) : null}

      {confirmDialog ? (
        <div className="modal-overlay open" onClick={() => closeConfirmDialog(false)}>
          <div className="modal" style={{ maxWidth: 460 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className={confirmDialog.iconClassName}></i> {confirmDialog.title}</h3>
              <button className="modal-close" type="button" onClick={() => closeConfirmDialog(false)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>{confirmDialog.message}</p>
            <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
              {confirmDialog.cancelLabel !== null ? (
                <button type="button" className="btn btn-outline btn-sm" onClick={() => closeConfirmDialog(false)}>
                  {confirmDialog.cancelLabel || 'Cancel'}
                </button>
              ) : null}
              <button type="button" className={confirmDialog.confirmClassName} onClick={() => closeConfirmDialog(true)}>{confirmDialog.confirmLabel}</button>
            </div>
          </div>
        </div>
      ) : null}

      {departmentEdit ? (
        <div className="modal-overlay open" onClick={() => setDepartmentEdit(null)}>
          <div className="modal" style={{ maxWidth: 680 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-pen"></i> Edit Department</h3>
              <button className="modal-close" type="button" onClick={() => setDepartmentEdit(null)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <form onSubmit={(event) => void handleUpdateDepartment(event)}>
              <div className="form-group">
                <label className="form-label">Department Code</label>
                <input
                  type="text"
                  className="form-control"
                  value={departmentEdit.code}
                  onChange={(event) => setDepartmentEdit((prev) => prev ? { ...prev, code: event.target.value.toUpperCase() } : prev)}
                  required
                />
              </div>
              <div className="form-group">
                <label className="form-label">Department Full Name</label>
                <input
                  type="text"
                  className="form-control"
                  value={departmentEdit.name}
                  onChange={(event) => setDepartmentEdit((prev) => prev ? { ...prev, name: event.target.value } : prev)}
                  required
                />
              </div>
              <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => setDepartmentEdit(null)}>Cancel</button>
                <button type="submit" className="btn btn-primary btn-sm"><i className="fas fa-save"></i> Save Changes</button>
              </div>
            </form>
          </div>
        </div>
      ) : null}

      {departmentActionState ? (
        <div className="modal-overlay open" onClick={() => { if (!departmentActionLoading) setDepartmentActionState(null); }}>
          <div className="modal" style={{ maxWidth: 460 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3>
                <i className={`fas ${departmentActionState.kind === 'toggle' ? 'fa-triangle-exclamation' : 'fa-trash'}`}></i>{' '}
                {departmentActionState.kind === 'toggle'
                  ? `${departmentActionState.department.is_active ? 'Disable' : 'Enable'} Department`
                  : 'Delete Department'}
              </h3>
              <button className="modal-close" type="button" onClick={() => setDepartmentActionState(null)} disabled={departmentActionLoading}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>
              {departmentActionState.kind === 'toggle'
                ? `${departmentActionState.department.is_active ? 'Disable' : 'Enable'} ${departmentActionState.department.code}? Counselors under this department will immediately follow the updated availability state.`
                : `Delete ${departmentActionState.department.code}? This removes the department from the rebuild database and cannot be undone.`}
            </p>
            <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => setDepartmentActionState(null)} disabled={departmentActionLoading}>Cancel</button>
              <button
                type="button"
                className={`btn btn-sm ${departmentActionState.kind === 'toggle' ? 'btn-warning' : 'btn-danger'}`}
                onClick={() => void handleConfirmDepartmentAction()}
                disabled={departmentActionLoading}
              >
                <i className={`fas ${departmentActionLoading ? 'fa-spinner fa-spin' : departmentActionState.kind === 'toggle' ? 'fa-power-off' : 'fa-trash'}`}></i>
                {departmentActionLoading
                  ? 'Working...'
                  : departmentActionState.kind === 'toggle'
                    ? (departmentActionState.department.is_active ? 'Disable' : 'Enable')
                    : 'Delete'}
              </button>
            </div>
          </div>
        </div>
      ) : null}

      {pendingConfigTab ? (
        <div className="modal-overlay open" onClick={() => setPendingConfigTab(null)}>
          <div className="modal" style={{ maxWidth: 480 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-floppy-disk"></i> Unsaved Settings</h3>
              <button className="modal-close" type="button" onClick={() => setPendingConfigTab(null)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 14 }}>
              You have unsaved settings changes. Save them before leaving Settings, or discard them and continue.
            </p>
            <div className="btn-group" style={{ justifyContent: 'flex-end', gap: 8 }}>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => setPendingConfigTab(null)} disabled={configSaving}>
                Stay
              </button>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => discardConfigChanges(pendingConfigTab)} disabled={configSaving}>
                Discard
              </button>
              <button
                type="button"
                className="btn btn-primary btn-sm"
                onClick={() => {
                  if (otpPolicyChanged) {
                    const nextTab = pendingConfigTab;
                    setPendingConfigTab(null);
                    setConfigPromptPassword('');
                    setConfigPasswordPrompt({ nextTab });
                    return;
                  }
                  void (async () => {
                    const result = await persistConfig('');
                    if (!result) return;
                    const nextTab = pendingConfigTab;
                    setPendingConfigTab(null);
                    if (!result.relogin && nextTab) {
                      setActiveTab(nextTab);
                      setMobileSidebarOpen(false);
                    }
                  })();
                }}
                disabled={configSaving}
              >
                <i className={`fas ${configSaving ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> {configSaving ? 'Saving...' : 'Save And Leave'}
              </button>
            </div>
          </div>
        </div>
      ) : null}

      {configPasswordPrompt ? (
        <div className="modal-overlay open" onClick={() => { if (!configSaving) setConfigPasswordPrompt(null); }}>
          <div className="modal" style={{ maxWidth: 460 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-key"></i> Confirm OTP Policy Change</h3>
              <button className="modal-close" type="button" onClick={() => setConfigPasswordPrompt(null)} disabled={configSaving}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 12 }}>
              Saving this change updates the OTP login policy and immediately logs out all active users.
            </p>
            <div className="form-group">
              <label className="form-label">Admin Password</label>
              <input
                className="form-control"
                type="password"
                value={configPromptPassword}
                onChange={(event) => setConfigPromptPassword(event.target.value)}
                placeholder="Enter your admin password"
                autoFocus
              />
            </div>
            <div className="btn-group" style={{ justifyContent: 'flex-end', gap: 8 }}>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => setConfigPasswordPrompt(null)} disabled={configSaving}>Cancel</button>
              <button type="button" className="btn btn-primary btn-sm" onClick={() => void handleConfirmConfigPassword()} disabled={configSaving}>
                <i className={`fas ${configSaving ? 'fa-spinner fa-spin' : 'fa-save'}`}></i> {configSaving ? 'Saving...' : 'Confirm And Save'}
              </button>
            </div>
          </div>
        </div>
      ) : null}

      {databaseBackupAction ? (
        <div className="modal-overlay open" onClick={() => { if (!databaseActionLoading) setDatabaseBackupAction(null); }}>
          <div className="modal" style={{ maxWidth: 460 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-triangle-exclamation"></i> {databaseBackupAction.kind === 'restore'
                ? 'Restore Backup'
                : databaseBackupAction.kind === 'archive'
                  ? 'Archive Academic Year'
                  : databaseBackupAction.kind === 'clear'
                    ? 'Clear Active Database'
                  : databaseBackupAction.kind === 'restore-archive'
                    ? 'Restore Archive'
                    : databaseBackupAction.kind === 'delete-archive'
                      ? 'Delete Archive'
                      : 'Delete Backup'}</h3>
              <button className="modal-close" type="button" onClick={() => setDatabaseBackupAction(null)} disabled={databaseActionLoading}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 12 }}>
              {databaseBackupAction.kind === 'restore'
                ? `Restore backup ${databaseBackupAction.backupName}? This logs out all users and replaces the current database.`
                : databaseBackupAction.kind === 'archive'
                  ? `Archive the active academic year as ${databaseBackupAction.backupName} and reset the live workspace?`
                  : databaseBackupAction.kind === 'clear'
                    ? 'Clear the active database workspace now? This removes current operational exam and notice data from the live workspace.'
                  : databaseBackupAction.kind === 'restore-archive'
                    ? `Restore archive ${databaseBackupAction.backupName}? This logs out all users and replaces the current database with the selected academic year.`
                    : databaseBackupAction.kind === 'delete-archive'
                      ? `Delete archive ${databaseBackupAction.backupName}? This cannot be undone.`
                      : `Delete backup ${databaseBackupAction.backupName}? This cannot be undone.`}
            </p>
            <form onSubmit={(event) => void handleConfirmDatabaseBackupAction(event)}>
              <div className="form-group">
                <label className="form-label">Confirm Password</label>
                <input className="form-control" type="password" value={databaseActionPassword} onChange={(event) => setDatabaseActionPassword(event.target.value)} required placeholder="Enter your password" />
              </div>
              <div className="btn-group" style={{ justifyContent: 'flex-end', gap: 8 }}>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => setDatabaseBackupAction(null)} disabled={databaseActionLoading}>Cancel</button>
                <button
                  type="submit"
                  className={`btn btn-sm ${(databaseBackupAction.kind === 'restore' || databaseBackupAction.kind === 'restore-archive') ? 'btn-outline' : 'btn-danger'}`}
                  disabled={databaseActionLoading}
                >
                  <i className={`fas ${databaseActionLoading
                    ? 'fa-spinner fa-spin'
                    : (databaseBackupAction.kind === 'restore' || databaseBackupAction.kind === 'restore-archive')
                      ? 'fa-rotate-left'
                      : databaseBackupAction.kind === 'archive'
                        ? 'fa-box-archive'
                        : databaseBackupAction.kind === 'clear'
                          ? 'fa-trash-can'
                        : 'fa-trash'}`}></i>
                  {databaseActionLoading
                    ? 'Working...'
                    : (databaseBackupAction.kind === 'restore' || databaseBackupAction.kind === 'restore-archive')
                      ? 'Restore'
                      : databaseBackupAction.kind === 'archive'
                        ? 'Archive'
                        : databaseBackupAction.kind === 'clear'
                          ? 'Clear Database'
                        : 'Delete'}
                </button>
              </div>
            </form>
          </div>
        </div>
      ) : null}
    </>
  );
}

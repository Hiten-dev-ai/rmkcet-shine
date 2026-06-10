import { FormEvent, useEffect, useMemo, useRef, useState } from 'react';
import appCrestLogo from '../assets/logo.png';
import appWordmarkLogo from '../assets/shine-logo.png';
import {
  archiveAcademicYear,
  getActivityScopeReport,
  downloadActivityScopeReportPdf,
  cancelLoginOtp,
  cleanupSessions,
  completePasswordReset,
  createUserAccount,
  clearExamDatabase,
  createDatabaseBackup,
  createDepartment,
  deleteUserAccount,
  deleteAdminMessage,
  deleteAdminMessages,
  deleteAllCounselorStudentRows,
  deleteCounselorStudentRow,
  deleteDatabaseBackup,
  deleteNoticeRecord,
  deleteTest as deleteReportTest,
  deleteDepartment,
  forceLogoutSession,
  getActivityOverview,
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
  getDatabaseOverview,
  getDepartments,
  getMonitoringOverview,
  getNoticesOverview,
  getReportsOverview,
  getServerConsole,
  getSmtpStatus,
  getTestDetail,
  getUsers,
  login,
  logoutAllSessions,
  logout,
  requestPasswordReset,
  resetUserPassword,
  resendLoginOtp,
  restoreDatabaseBackup,
  runSmtpTest,
  saveTestMarks,
  saveNotice,
  saveCounselorStudentRow,
  saveTestMeta,
  sendSingleNotice,
  sendSingleReport,
  startTestMode,
  lockUserAccount,
  stopTestMode,
  sendSelfPasswordOtp,
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
  verifyLoginOtp,
  verifyPasswordResetOtp,
} from './api';
import type {
  ActivityOverviewPayload,
  ActivityScopeReportPayload,
  ActivityScopeReportSection,
  AdminMessagesOverviewPayload,
  AdminMessageRecord,
  AuthUser,
  BootstrapPayload,
  ConfigOverviewPayload,
  DashboardOverviewPayload,
  CounselorMessageRecord,
  CounselorMessageStats,
  CounselorNoticeSendPagePayload,
  CounselorStudentRecord,
  CounselorSendNoticeRow,
  CounselorActivityRow,
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
  ReportStudentRow,
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
  TestDetailPayload,
  UserRecord,
} from './types';

type LoginState = {
  identifier: string;
  password: string;
  otp_code: string;
  loading: boolean;
  error: string;
  conflict: SessionConflict | null;
};

type LoginOtpState = {
  maskedEmail: string;
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
  reports: 'Reports',
  notices: 'Notices',
  departments: 'Departments',
  activity: 'Counsellor Activity',
  users: 'Users',
  database: 'Database',
  monitoring: 'Session Monitoring',
  'server-console': 'Server Console',
  messages: 'Message Logs',
  config: 'Settings',
};

const DEFAULT_ADMIN_MESSAGES_LIMIT = 300;
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

type FieldOrderEntry =
  | { type: 'subject'; label: string; rawKey: string; normalizedKey: string }
  | { type: 'metric'; metricKey: 'failed_subjects' | 'not_attended' | 'gpa'; label: string };

type BackupActionState = {
  kind: 'restore' | 'delete';
  backupName: string;
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

function getTabsForUser(user: AuthUser | null) {
  if (!user) return [];
  if (user.role === 'admin') {
    return ['dashboard', 'reports', 'notices', 'departments', 'activity', 'users', 'database', 'monitoring', 'messages', 'server-console'];
  }
  if (user.role === 'principal') {
    return ['dashboard', 'reports', 'notices', 'departments', 'activity', 'users', 'database'];
  }
  if (user.role === 'hod') {
    return ['dashboard', 'reports', 'notices', 'activity', 'messages'];
  }
  if (user.role === 'deo') {
    return ['reports', 'notices', 'activity', 'users', 'messages'];
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
    reports: 'fa-file-lines',
    notices: 'fa-bullhorn',
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
  if (user.role === 'principal') return 'PRINCIPAL';
  if (user.role === 'counselor') return 'COUNSELOR';
  return 'ADMIN';
}

function getRoleOptionLabel(role: Role) {
  if (role === 'admin') return 'System Admin';
  if (role === 'principal') return 'Principal';
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
    </div>
  );
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

function buildNoticeCopyLines(rows: NoticeCompletionRow[]) {
  const pendingRows = rows
    .filter((row) => (row.pending_notice_count || 0) > 0)
    .sort((a, b) =>
      a.department.localeCompare(b.department)
      || (a.year_level || 1) - (b.year_level || 1)
      || a.name.localeCompare(b.name),
    );
  const lines: CopyLine[] = [
    { tone: 'body', text: 'The Following Counsellors are yet to send the specified Notices' },
    { tone: 'spacer', text: '' },
  ];
  let lastScope = '';
  for (const row of pendingRows) {
    const scopeKey = `${row.department}::${row.year_level}`;
    if (scopeKey !== lastScope) {
      lines.push({ tone: 'section', text: row.department });
      lines.push({ tone: 'subsection', text: formatYearLevel(row.year_level || 1) });
      lastScope = scopeKey;
    }
    lines.push({ tone: 'name', text: `*${row.name}*` });
    for (const title of row.pending_notice_titles || []) {
      lines.push({ tone: 'bullet', text: `- ${title}` });
    }
    lines.push({ tone: 'spacer', text: '' });
  }
  return lines;
}

function buildActivityCopyLines(
  sections: ActivityScopeReportSection[],
  mode: 'scope' | 'department' | 'year' | 'test',
) {
  const lines: CopyLine[] = [
    { tone: 'body', text: 'The Following are all the counsellors who are yet to send results to their respective students' },
    { tone: 'spacer', text: '' },
  ];

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
    lines.push({ tone: 'section', text: department });
    for (const [yearLevel, semesterMap] of yearMap.entries()) {
      lines.push({ tone: 'subsection', text: formatYearLevel(yearLevel) });
      for (const [semester, counselorMap] of semesterMap.entries()) {
        lines.push({ tone: 'subsection', text: formatSemesterBadge(semester) });
        const counselorEntries = Array.from(counselorMap.entries())
          .filter(([key]) => !key.startsWith('__name__:'))
          .map(([key, tests]) => ({
            name: counselorMap.get(`__name__:${key}`)?.[0] || key,
            tests: Array.from(new Set(tests)),
          }))
          .sort((a, b) => a.name.localeCompare(b.name));
        for (const counselor of counselorEntries) {
          lines.push({ tone: 'name', text: `*${counselor.name}*` });
          for (const testName of counselor.tests) {
            lines.push({ tone: 'bullet', text: `- ${testName}` });
          }
        }
        lines.push({ tone: 'spacer', text: '' });
      }
    }
  }

  return lines;
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

function splitTestsBySemester<T extends { semester: string }>(tests: T[]) {
  return {
    sem1: tests.filter((test) => String(test.semester || '').trim() === '1'),
    sem2: tests.filter((test) => String(test.semester || '').trim() === '2'),
  };
}

function toBooleanString(value: string | undefined) {
  return String(value || '').trim().toLowerCase() === 'true';
}

function formatDateTime(value: string | null | undefined) {
  const raw = String(value || '').trim();
  if (!raw) return '--';
  return raw.slice(0, 16).replace('T', ' ');
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

function openWhatsAppAppDirect(waLink: string) {
  const appLink = resolveWaLinkByMode(waLink, 'app');
  if (!appLink) return false;
  if (isMobileUi()) {
    window.location.assign(appLink);
    return true;
  }
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
      window.location.assign(appLink);
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
    window.location.assign(webLink);
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
  const [bootstrap, setBootstrap] = useState<BootstrapPayload | null>(null);
  const [bootLoading, setBootLoading] = useState(true);
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
  });
  const [loginOtpState, setLoginOtpState] = useState<LoginOtpState | null>(null);
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
    department: '',
    year_level: '1',
    max_students: '30',
    scope_pairs: [] as string[],
  });
  const [userSaving, setUserSaving] = useState(false);
  const [userEditDraft, setUserEditDraft] = useState<{
    original_email: string;
    name: string;
    email: string;
    password: string;
    role: Role;
    department: string;
    year_level: string;
    max_students: string;
    scope_pairs: string[];
  } | null>(null);
  const [userActionTarget, setUserActionTarget] = useState<{ kind: 'lock' | 'unlock' | 'delete'; user: UserRecord } | null>(null);
  const [userActionLoading, setUserActionLoading] = useState(false);
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
    sendMode: 'app' as 'app' | 'web',
  });
  const [counselorNoticeAutoTemplate, setCounselorNoticeAutoTemplate] = useState('');
  const [counselorNoticeTemplateEdited, setCounselorNoticeTemplateEdited] = useState(false);
  const [counselorNoticeBatchRunning, setCounselorNoticeBatchRunning] = useState(false);
  const [counselorNoticeBatchIndex, setCounselorNoticeBatchIndex] = useState(0);
  const [counselorNoticeBatchLastStudent, setCounselorNoticeBatchLastStudent] = useState('');
  const [counselorNoticeIncludeGenerated, setCounselorNoticeIncludeGenerated] = useState(false);
  const [reportsLoading, setReportsLoading] = useState(false);
  const [reportsData, setReportsData] = useState<ReportsOverviewPayload | null>(null);
  const [counselorOverviewLoading, setCounselorOverviewLoading] = useState(false);
  const [counselorOverview, setCounselorOverview] = useState<CounselorOverviewPayload | null>(null);
  const [counselorTestsLoading, setCounselorTestsLoading] = useState(false);
  const [counselorTests, setCounselorTests] = useState<CounselorVisibleTestRecord[]>([]);
  const [counselorMessagesLoading, setCounselorMessagesLoading] = useState(false);
  const [counselorMessages, setCounselorMessages] = useState<CounselorMessageRecord[]>([]);
  const [counselorMessageStats, setCounselorMessageStats] = useState<CounselorMessageStats | null>(null);
  const [counselorSendVerify, setCounselorSendVerify] = useState<CounselorSendVerifyState | null>(null);
  const [counselorSendLoading, setCounselorSendLoading] = useState(false);
  const [counselorSendPage, setCounselorSendPage] = useState<CounselorSendPagePayload | null>(null);
  const [counselorSendVars, setCounselorSendVars] = useState({
    test_name: '',
    semester: '',
    batch_name: '',
    template: DEFAULT_REPORT_TEMPLATE,
    sendMode: 'app' as 'app' | 'web',
  });
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
  const [testMetaDraft, setTestMetaDraft] = useState({ test_name: '', semester: '', batch_name: '', section: '' });
  const [savingMeta, setSavingMeta] = useState(false);
  const [savingMarks, setSavingMarks] = useState(false);
  const [uploadingReport, setUploadingReport] = useState(false);
  const [reportUploadInputKey, setReportUploadInputKey] = useState(0);
  const [reportUploadDraft, setReportUploadDraft] = useState({
    test_name: '',
    semester: '',
    batch_name: '',
    section: '',
    upload_mode: 'new',
    file: null as File | null,
  });
  const [dashboardLoading, setDashboardLoading] = useState(false);
  const [dashboardData, setDashboardData] = useState<DashboardOverviewPayload | null>(null);
  const [activityLoading, setActivityLoading] = useState(false);
  const [activityData, setActivityData] = useState<ActivityOverviewPayload | null>(null);
  const [activityFilters, setActivityFilters] = useState({
    department: '',
    year: '',
    semester: '',
    test_name: '',
    q: '',
    sort: 'pending_first',
  });
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
  const [monitoringLoading, setMonitoringLoading] = useState(false);
  const [monitoringData, setMonitoringData] = useState<MonitoringOverviewPayload | null>(null);
  const [databaseLoading, setDatabaseLoading] = useState(false);
  const [databaseData, setDatabaseData] = useState<DatabaseOverviewPayload | null>(null);
  const [databaseBatchName, setDatabaseBatchName] = useState('');
  const [databaseOverwrite, setDatabaseOverwrite] = useState(false);
  const [databaseBackupAction, setDatabaseBackupAction] = useState<BackupActionState>(null);
  const [databaseActionPassword, setDatabaseActionPassword] = useState('');
  const [databaseActionLoading, setDatabaseActionLoading] = useState(false);
  const [clearExamPassword, setClearExamPassword] = useState('');
  const [archiveYearLabel, setArchiveYearLabel] = useState('');
  const [archiveYearOverwrite, setArchiveYearOverwrite] = useState(false);
  const [archiveYearLoading, setArchiveYearLoading] = useState(false);
  const [databaseProgress, setDatabaseProgress] = useState<DatabaseProgressState>(null);
  const [configLoading, setConfigLoading] = useState(false);
  const [configData, setConfigData] = useState<ConfigOverviewPayload | null>(null);
  const [configForm, setConfigForm] = useState<Record<string, string | boolean>>({});
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
  const [resetUserDepartmentFilter, setResetUserDepartmentFilter] = useState('');
  const [resetUserYearFilter, setResetUserYearFilter] = useState('');
  const [previewUserSearch, setPreviewUserSearch] = useState('');
  const [previewUserEmail, setPreviewUserEmail] = useState('');
  const [resetSaving, setResetSaving] = useState(false);
  const [serverConsoleLoading, setServerConsoleLoading] = useState(false);
  const [serverConsoleData, setServerConsoleData] = useState<ServerConsolePayload | null>(null);
  const [theme, setTheme] = useState<'light' | 'dark'>(() => {
    try {
      return (localStorage.getItem('theme') as 'light' | 'dark') || 'light';
    } catch {
      return 'light';
    }
  });
  const selectedAdminMessageIdSet = useMemo(() => new Set(selectedAdminMessageIds), [selectedAdminMessageIds]);
  const counselorBatchTimerRef = useRef<number | null>(null);
  const counselorBatchQueueRef = useRef<CounselorSendReportRow[]>([]);
  const counselorBatchIndexRef = useRef(0);
  const counselorBatchRunningRef = useRef(false);
  const counselorNoticeBatchTimerRef = useRef<number | null>(null);
  const noticeComposerRef = useRef<HTMLDivElement | null>(null);
  const confirmResolverRef = useRef<((value: boolean) => void) | null>(null);
  const counselorNoticeBatchQueueRef = useRef<CounselorSendNoticeRow[]>([]);
  const counselorNoticeBatchIndexRef = useRef(0);
  const counselorNoticeBatchRunningRef = useRef(false);
  const counselorSendReturnRestoreRef = useRef(false);

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
    void (async () => {
      try {
        const payload = await getBootstrap();
        setBootstrap(payload);
        applyThemeColors(payload.appConfig);
        if (payload.user) {
          setActiveTab(payload.defaultTab || getDefaultTab(payload.user));
        }
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

    if (success === '1') {
      setFlash({ type: 'success', message: 'Google sign-in completed successfully.' });
      void refreshBootstrap();
    } else if (error) {
      let message = 'Google sign-in could not be completed.';
      if (error === 'google_disabled') message = 'Google sign-in is not enabled right now.';
      else if (error === 'state_mismatch') message = 'Google sign-in state validation failed. Please try again.';
      else if (error === 'missing_code') message = 'Google sign-in did not return an authorization code.';
      else if (error === 'token_exchange_failed') message = 'Google sign-in token exchange failed.';
      else if (error === 'invalid_google_profile') message = 'Google sign-in did not return a valid verified email.';
      else if (error === 'invalid_domain') message = allowedDomain ? `Only ${allowedDomain} Google accounts are allowed.` : 'This Google account is not allowed.';
      else if (error === 'user_not_linked') message = 'Account not registered.';
      else if (error === 'access_denied') message = errorDescription || 'Google account access is blocked.';
      else if (errorDescription) message = errorDescription;
      setFlash({ type: 'error', message });
    }

    params.delete('auth');
    params.delete('error');
    params.delete('error_description');
    params.delete('allowed_domain');
    params.delete('success');
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

    setUsersLoading(true);
    void getUsers()
      .then((payload) => {
        setUsers(payload.users);
        setDepartments(payload.departments);
        setUserActorScopes(payload.actorScopes || []);
        setUserAssignableRoles(payload.assignableRoles || []);
        setUserCreateForm((prev) => ({
          ...prev,
          role: (payload.assignableRoles?.[0] || prev.role || 'counselor') as Role,
        }));
      })
      .finally(() => setUsersLoading(false));
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

    setReportsLoading(true);
    void getReportsOverview()
      .then((payload) => setReportsData(payload))
      .finally(() => setReportsLoading(false));
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
    if (bootstrap.counselorOverview) {
      setCounselorOverview((prev) => prev || bootstrap.counselorOverview || null);
    }
    if (bootstrap.counselorTests?.length) {
      setCounselorTests((prev) => (prev.length ? prev : bootstrap.counselorTests || []));
    }
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
    const query = userSearch.trim().toLowerCase();
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
      if (userSortBy === 'role') return getRoleOptionLabel(a.role).localeCompare(getRoleOptionLabel(b.role));
      if (userSortBy === 'department') return String(a.department || '').localeCompare(String(b.department || ''));
      if (userSortBy === 'year') return Number(a.year_level || 0) - Number(b.year_level || 0);
      return a.name.localeCompare(b.name);
    });
    return sorted;
  }, [userFilterDepartment, userFilterRole, userFilterStatus, userFilterStudentList, userFilterYear, userSearch, userSortBy, users]);
  const filteredResetUsers = useMemo(() => {
    const allUsers = configData?.resetUsers || [];
    const query = resetUserSearch.trim().toLowerCase();
    const filtered = allUsers.filter((row) => {
      const matchesQuery = !query || [row.name, row.email, row.role, row.department || ''].join(' ').toLowerCase().includes(query);
      const matchesDepartment = !resetUserDepartmentFilter || String(row.department || '').toUpperCase() === resetUserDepartmentFilter.toUpperCase();
      const matchesYear = !resetUserYearFilter || String(row.year_level || '') === resetUserYearFilter;
      return matchesQuery && matchesDepartment && matchesYear;
    });
    if (!query && !resetUserDepartmentFilter && !resetUserYearFilter) return filtered.slice(0, 12);
    return filtered.slice(0, 20);
  }, [configData?.resetUsers, resetUserDepartmentFilter, resetUserSearch, resetUserYearFilter]);
  const resetFilterDepartments = useMemo(
    () => Array.from(new Set((configData?.resetUsers || []).map((row) => String(row.department || '').trim()).filter(Boolean))).sort((a, b) => a.localeCompare(b)),
    [configData?.resetUsers],
  );
  const resetFilterYears = useMemo(
    () => Array.from(new Set((configData?.resetUsers || []).map((row) => Number(row.year_level || 0)).filter((value) => value > 0))).sort((a, b) => a - b),
    [configData?.resetUsers],
  );
  const filteredPreviewUsers = useMemo(() => {
    const allUsers = configData?.resetUsers || [];
    const query = previewUserSearch.trim().toLowerCase();
    if (!query) return allUsers.slice(0, 12);
    return allUsers
      .filter((row) => [row.name, row.email, row.role, row.department || ''].join(' ').toLowerCase().includes(query))
      .slice(0, 12);
  }, [configData?.resetUsers, previewUserSearch]);
  const filteredAdminMessageSuggestions = useMemo(() => {
    const allSuggestions = adminMessagesData?.suggestions || [];
    const query = adminMessageSearch.trim().toLowerCase();
    if (!query) return allSuggestions.slice(0, 12);
    return allSuggestions
      .filter((item) => [item.name || '', item.email || ''].join(' ').toLowerCase().includes(query))
      .slice(0, 12);
  }, [adminMessageSearch, adminMessagesData?.suggestions]);
  const previewUserRecord = useMemo(
    () => (configData?.resetUsers || []).find((row) => row.email === previewUserEmail) || null,
    [configData?.resetUsers, previewUserEmail],
  );
  const previewShellUser = useMemo(
    () => previewUserRecord ? {
      email: previewUserRecord.email,
      name: previewUserRecord.name,
      role: previewUserRecord.role,
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
  const selectedAdminMessageSuggestion = useMemo(() => {
    const needle = String(adminMessageFilters.q || adminMessageSearch || '').trim().toLowerCase();
    if (!needle) return null;
    return (adminMessagesData?.suggestions || []).find((item) => {
      const name = String(item.name || '').trim().toLowerCase();
      const email = String(item.email || '').trim().toLowerCase();
      return name === needle || email === needle;
    }) || null;
  }, [adminMessageFilters.q, adminMessageSearch, adminMessagesData?.suggestions]);
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
  const activityDisplayRows = useMemo(() => {
    const rows = [...(activityData?.result?.rows || [])];
    const query = String(activityFilters.q || '').trim().toLowerCase();
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
  }, [activityData?.result?.rows, activityFilters.q, activityFilters.sort]);
  const reportTestsBySemester = useMemo(() => splitTestsBySemester(reportsData?.tests || []), [reportsData]);
  const counselorVisibleTests = useMemo(() => {
    if (counselorTests.length) return counselorTests;
    if (bootstrap?.counselorTests?.length) return bootstrap.counselorTests;
    if (counselorOverview?.recentTests?.length) return counselorOverview.recentTests;
    if (bootstrap?.counselorOverview?.recentTests?.length) return bootstrap.counselorOverview.recentTests;
    return [];
  }, [bootstrap?.counselorOverview?.recentTests, bootstrap?.counselorTests, counselorOverview?.recentTests, counselorTests]);
  const counselorTestsBySemester = useMemo(() => splitTestsBySemester(counselorVisibleTests), [counselorVisibleTests]);
  const counselorDashboardRecentTests = useMemo(() => {
    if (counselorOverview?.recentTests?.length) return counselorOverview.recentTests;
    if (bootstrap?.counselorOverview?.recentTests?.length) return bootstrap.counselorOverview.recentTests;
    return counselorVisibleTests.slice(0, 2);
  }, [bootstrap?.counselorOverview?.recentTests, counselorOverview?.recentTests, counselorVisibleTests]);
  const counselorTopPerformingStudents = useMemo(() => {
    if (counselorOverview?.topPerformingStudents?.length) return counselorOverview.topPerformingStudents;
    if (bootstrap?.counselorOverview?.topPerformingStudents?.length) return bootstrap.counselorOverview.topPerformingStudents;
    return [];
  }, [bootstrap?.counselorOverview?.topPerformingStudents, counselorOverview?.topPerformingStudents]);
  const counselorStudentsNeedImprovement = useMemo(() => {
    if (counselorOverview?.studentsNeedImprovement?.length) return counselorOverview.studentsNeedImprovement;
    if (bootstrap?.counselorOverview?.studentsNeedImprovement?.length) return bootstrap.counselorOverview.studentsNeedImprovement;
    return [];
  }, [bootstrap?.counselorOverview?.studentsNeedImprovement, counselorOverview?.studentsNeedImprovement]);
  const counselorDashboardPendingNotices = useMemo(() => {
    if (counselorOverview?.pendingNotices?.length) return counselorOverview.pendingNotices;
    if (bootstrap?.counselorOverview?.pendingNotices?.length) return bootstrap.counselorOverview.pendingNotices;
    return [];
  }, [bootstrap?.counselorOverview?.pendingNotices, counselorOverview?.pendingNotices]);

  const currentUser = bootstrap?.user || null;
  const canOpenFooterTemplates = currentUser?.role === 'admin' || currentUser?.role === 'deo';
  const isTestMode = Boolean(bootstrap?.testMode?.active);
  const navTabs = bootstrap?.navTabs?.length ? bootstrap.navTabs : getTabsForUser(currentUser);
  const smtpIndicator = useMemo(
    () => getSmtpIndicator(bootstrap?.appConfig || null, bootstrap?.authUi || null),
    [bootstrap?.appConfig, bootstrap?.authUi],
  );
  const sidebarDepartmentCodes = useMemo(() => getUserDepartmentCodes(currentUser).slice(0, 6), [currentUser]);
  const testMetaReadOnly = Boolean(testDetail?.isMetaReadOnly ?? testDetail?.isReadOnly);
  const testMarksReadOnly = Boolean(testDetail?.isMarksReadOnly ?? testDetail?.isReadOnly);
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

  async function refreshBootstrap() {
    const payload = await getBootstrap();
    const previousEmail = String(bootstrap?.user?.email || '').toLowerCase();
    const nextEmail = String(payload.user?.email || '').toLowerCase();
    const userChanged = previousEmail !== nextEmail;
    setBootstrap(payload);
    applyThemeColors(payload.appConfig);
    if (!payload.user) {
      setLoginOtpState(null);
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
    const allowHiddenConfig = activeTab === 'config' && payload.user.role === 'admin';
    if (!payload.navTabs.includes(activeTab) && !allowHiddenConfig) {
      setActiveTab(payload.defaultTab || getDefaultTab(payload.user));
    }
    setMobileSidebarOpen(false);
  }

  async function handleStartAccountTestMode(email: string) {
    try {
      await startTestMode(email);
      await refreshBootstrap();
      setPreviewUserEmail('');
      setPreviewUserSearch('');
      setFlash({ type: 'success', message: 'Entered account test mode.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to start account test mode.' });
    }
  }

  async function handleExitTestMode() {
    try {
      await stopTestMode();
      await refreshBootstrap();
      setActiveTab('config');
      setFlash({ type: 'success', message: 'Exited test mode.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to exit test mode.' });
    }
  }

  async function handleLogin(event: FormEvent<HTMLFormElement>, forceLogout = false) {
    event.preventDefault();
    setLoginState((prev) => ({ ...prev, loading: true, error: '', conflict: null }));
    try {
      const result = await login(loginState.identifier, loginState.password, forceLogout);
      if (result?.requiresOtp) {
        setLoginOtpState({ maskedEmail: String(result.maskedEmail || '') });
        setLoginState((prev) => ({ ...prev, otp_code: '', loading: false, error: '', conflict: null }));
        return;
      }
      await refreshBootstrap();
    } catch (error) {
      const err = error as Error & { payload?: any; status?: number };
      if (err.status === 409 && err.payload?.requiresForceLogout) {
        setLoginState((prev) => ({
          ...prev,
          loading: false,
          error: '',
          conflict: err.payload.existingSession || null,
        }));
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
    });
  }

  async function handleVerifyLoginOtp(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setLoginState((prev) => ({ ...prev, loading: true, error: '' }));
    try {
      await verifyLoginOtp(loginState.otp_code);
      await refreshBootstrap();
      setLoginState({
        identifier: '',
        password: '',
        otp_code: '',
        loading: false,
        error: '',
        conflict: null,
      });
      setLoginOtpState(null);
    } catch (error) {
      setLoginState((prev) => ({
        ...prev,
        loading: false,
        error: error instanceof Error ? error.message : 'OTP verification failed.',
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
    setLoginState((prev) => ({ ...prev, otp_code: '', loading: false, error: '', conflict: null }));
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

  async function refreshUsersOverview() {
    if (!currentUser || !['admin', 'principal', 'deo'].includes(currentUser.role)) return;
    setUsersLoading(true);
    try {
      const payload = await getUsers();
      setUsers(payload.users);
      setDepartments(payload.departments);
      setUserActorScopes(payload.actorScopes || []);
      setUserAssignableRoles(payload.assignableRoles || []);
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
      const payload = await getCounselorStudentList(user.email);
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
      await refreshUsersOverview();
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
      setFlash({ type: 'success', message: 'Student saved successfully.' });
      await loadCounselorStudents(studentListCounselor);
      await refreshUsersOverview();
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
      await refreshUsersOverview();
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
      await refreshUsersOverview();
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

  async function loadReports(department?: string, year?: number | null) {
    setReportsLoading(true);
    try {
      const payload = await getReportsOverview(department, year);
      setReportsData(payload);
      setTestDetail(null);
    } finally {
      setReportsLoading(false);
    }
  }

  async function loadDashboardOverview() {
    setDashboardLoading(true);
    try {
      const payload = await getDashboardOverview();
      setDashboardData(payload);
    } catch (error) {
      setDashboardData(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to load dashboard overview.' });
    } finally {
      setDashboardLoading(false);
    }
  }

  async function loadActivityOverview(filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
    q?: string;
    sort?: string;
  }) {
    setActivityLoading(true);
    try {
      const payload = await getActivityOverview(filters);
      setActivityData(payload);
      setActivityFilters({
        department: payload.selectedDepartment || '',
        year: payload.selectedYear ? String(payload.selectedYear) : '',
        semester: payload.selectedSemester || '',
        test_name: payload.selectedTestName || '',
        q: payload.searchQuery || '',
        sort: payload.sortMode || 'pending_first',
      });
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
    setConfigForm({
      enable_counselor_batch_send: toBooleanString(payload.appConfig.enable_counselor_batch_send),
      counselor_batch_send_delay_seconds: payload.appConfig.counselor_batch_send_delay_seconds || '4',
      current_batch_year: payload.appConfig.current_batch_year || '',
      session_timeout_hours: String(Math.max(1, Math.round((Number(payload.appConfig.session_timeout || 86400) || 86400) / 3600))),
      session_heartbeat_interval: payload.appConfig.session_heartbeat_interval || '30',
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
      counselor_login_otp_enabled: toBooleanString(payload.appConfig.counselor_login_otp_enabled),
      notice_copy_as_image: toBooleanString(payload.appConfig.notice_copy_as_image),
      activity_copy_as_image: toBooleanString(payload.appConfig.activity_copy_as_image),
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
    });
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

  async function openCounselorSendPage(testId: number, mode: 'app' | 'web' = 'app') {
    setActiveTab('test-database');
    setCounselorSendVerify(null);
    setCounselorSendLoading(true);
    try {
      const payload = await getCounselorSendPage(testId, mode);
      const defaultOrder = buildDefaultOrderList(payload.rows);
      let storedValues: Partial<typeof counselorSendVars> = {};
      try {
        storedValues = JSON.parse(localStorage.getItem(`send_common_vars_${payload.testId}`) || '{}');
      } catch {
        storedValues = {};
      }

      setCounselorSendPage(payload);
      setCounselorDefaultFieldOrder(defaultOrder.map((item) => ({ ...item })));
      setCounselorFieldOrder(defaultOrder.map((item) => ({ ...item })));
      setCounselorSendVars({
        test_name: String(storedValues.test_name || payload.meta.test_name || ''),
        semester: String(storedValues.semester || payload.meta.semester || ''),
        batch_name: String(storedValues.batch_name || payload.meta.batch_name || payload.defaultBatchName || ''),
        template: String(storedValues.template || DEFAULT_REPORT_TEMPLATE),
        sendMode: payload.sendMode || 'app',
      });
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
    setActiveTab('test-database');
    setTestDetail(null);
    setCounselorSendPage(null);
    stopCounselorBatchSend();

    if (isMobileUi()) {
      void openCounselorSendPage(testId, 'app');
      return;
    }

    setCounselorSendVerify({
      testId,
      testName: testName || 'Selected Test',
      appFound: false,
      completed: false,
      tone: 'neutral',
      title: 'Checking...',
      body: 'Trying to open WhatsApp app using direct app link.',
    });
  }

  function installWhatsappAndReturn() {
    try {
      window.location.href = 'ms-windows-store://pdp/?ProductId=9NKSQGP7F2NH';
    } catch {
      // Ignore navigation failures.
    }
    setActiveTab('recent-tests');
    setCounselorSendVerify(null);
  }

  function stopCounselorNoticeBatchSend() {
    counselorNoticeBatchRunningRef.current = false;
    setCounselorNoticeBatchRunning(false);
    if (counselorNoticeBatchTimerRef.current) {
      window.clearTimeout(counselorNoticeBatchTimerRef.current);
      counselorNoticeBatchTimerRef.current = null;
    }
  }

  async function openCounselorNoticeSendPage(noticeId: number, mode: 'app' | 'web' = 'app') {
    setActiveTab('notices');
    setCounselorNoticeSendVerify(null);
    setCounselorNoticeSendLoading(true);
    try {
      const payload = await getCounselorNoticeSendPage(noticeId, mode);
      let storedValues: Partial<typeof counselorNoticeSendVars> = {};
      try {
        storedValues = JSON.parse(localStorage.getItem(`notice_send_vars_${payload.noticeId}`) || '{}');
      } catch {
        storedValues = {};
      }

      const defaultTemplate = String(storedValues.template || payload.defaultTemplate || '');
      setCounselorNoticeSendPage(payload);
      setCounselorNoticeSendVars({
        title: String(storedValues.title || payload.notice.title || ''),
        text: String(storedValues.text || payload.notice.message_text || ''),
        template: defaultTemplate,
        sendMode: payload.sendMode || 'app',
      });
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
    setActiveTab('notices');
    setCounselorNoticeSendPage(null);
    stopCounselorNoticeBatchSend();

    if (isMobileUi()) {
      void openCounselorNoticeSendPage(notice.id, 'app');
      return;
    }

    setCounselorNoticeSendVerify({
      noticeId: notice.id,
      noticeTitle: notice.title_display || notice.title || 'Selected Notice',
      appFound: false,
      completed: false,
      tone: 'neutral',
      title: 'Checking...',
      body: 'Trying to open WhatsApp app using direct app link.',
    });
  }

  function installWhatsappForNoticeAndReturn() {
    try {
      window.location.href = 'ms-windows-store://pdp/?ProductId=9NKSQGP7F2NH';
    } catch {
      // Ignore navigation failures.
    }
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
    formData.set('message_template', counselorSendVars.template || '');
    formData.set('test_name', counselorSendVars.test_name || '');
    formData.set('semester', counselorSendVars.semester || '');
    formData.set('batch_name', counselorSendVars.batch_name || '');
    formData.set('section', counselorSendPage.meta.section || '');
    formData.set('department', row.department || counselorSendPage.meta.department || '');
    formData.set('ordered_fields', JSON.stringify(getOrderedFieldPayload()));
    formData.set('send_mode', isMobileUi() ? 'app' : counselorSendVars.sendMode);
    for (const [key, value] of Object.entries(extra)) {
      formData.set(key, value);
    }
    return formData;
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

  async function handleCounselorSendSingle(row: CounselorSendReportRow) {
    const currentSendPage = counselorSendPage;
    if (!currentSendPage) return false;
    try {
      const prepared = await prepareSingleCounselorDelivery(row);
      if (!prepared.waLink) {
        throw new Error('Parent phone number is missing or invalid for this student.');
      }

      const effectiveSendMode = isMobileUi() ? 'app' : counselorSendVars.sendMode;
      if (effectiveSendMode === 'web') {
        await confirmSingleCounselorDelivery(row, prepared.deliveryToken, 'sent');
        markCounselorRowGenerated(row.reg_no);
        saveSendReturnState({
          kind: 'report',
          id: currentSendPage.testId,
          mode: 'web',
          timestamp: Date.now(),
        });
        if (!openWhatsAppWebDirect(prepared.waLink)) {
          throw new Error('Unable to open WhatsApp Web link.');
        }
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
    formData.set('message_template', counselorNoticeSendVars.template || '');
    formData.set('notice_title', counselorNoticeSendVars.title || '');
    formData.set('notice_text', counselorNoticeSendVars.text || '');
    formData.set('send_mode', isMobileUi() ? 'app' : counselorNoticeSendVars.sendMode);
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

  async function handleCounselorNoticeSendSingle(row: CounselorSendNoticeRow) {
    const currentSendPage = counselorNoticeSendPage;
    if (!currentSendPage) return false;
    try {
      const prepared = await prepareSingleCounselorNoticeDelivery(row);
      if (!prepared.waLink) {
        throw new Error('Parent phone number is missing or invalid for this student.');
      }

      const effectiveSendMode = isMobileUi() ? 'app' : counselorNoticeSendVars.sendMode;
      if (effectiveSendMode === 'web') {
        await confirmSingleCounselorNoticeDelivery(row, prepared.deliveryToken, 'sent');
        markCounselorNoticeRowGenerated(row.reg_no);
        saveSendReturnState({
          kind: 'notice',
          id: currentSendPage.noticeId,
          mode: 'web',
          timestamp: Date.now(),
        });
        if (!openWhatsAppWebDirect(prepared.waLink)) {
          throw new Error('Unable to open WhatsApp Web link.');
        }
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

  async function handleSaveMeta(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!testDetail) return;
    setSavingMeta(true);
    try {
      await saveTestMeta(testDetail.testId, testMetaDraft);
      setFlash({ type: 'success', message: 'Test metadata updated successfully.' });
      await loadTestDetail(testDetail.testId);
      if (reportsData?.selectedDepartment && reportsData.selectedYear) {
        await loadReports(reportsData.selectedDepartment, reportsData.selectedYear);
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
    for (const student of testDetail.students) {
      try {
        await saveTestMarks(testDetail.testId, {
          reg_no: student.reg_no,
          marks: Object.fromEntries(testDetail.subjects.map((subject) => [subject, student.marks[subject] || ''])),
        });
        successCount += 1;
      } catch {
        failCount += 1;
      }
    }
    setSavingMarks(false);
    if (failCount === 0) {
      setFlash({ type: 'success', message: `Saved marks for ${successCount} students.` });
    } else {
      setFlash({ type: 'warning', message: `Save finished. Success: ${successCount}, Failed: ${failCount}.` });
    }
  }

  async function handleToggleTestBlock(test: ReportTestRecord) {
    try {
      await toggleTestBlock(test.id);
      setFlash({ type: 'success', message: test.is_blocked ? 'Test unblocked.' : 'Test blocked.' });
      if (reportsData?.selectedDepartment && reportsData.selectedYear) {
        await loadReports(reportsData.selectedDepartment, reportsData.selectedYear);
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
      setFlash({ type: 'success', message: 'Test deleted successfully.' });
      if (testDetail?.testId === test.id) {
        setTestDetail(null);
      }
      if (reportsData?.selectedDepartment && reportsData.selectedYear) {
        await loadReports(reportsData.selectedDepartment, reportsData.selectedYear);
      }
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to delete test.' });
    }
  }

  async function handleUploadReport(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!reportsData?.selectedDepartment || !reportsData.selectedYear) return;
    if (!reportUploadDraft.file) {
      setFlash({ type: 'error', message: 'Please choose a marks file to upload.' });
      return;
    }

    setUploadingReport(true);
    try {
      const batchName = reportUploadDraft.batch_name || getDefaultBatchNameForYearLevel(reportsData.selectedYear, bootstrap?.appConfig || null);
      const formData = new FormData();
      formData.set('marks_file', reportUploadDraft.file);
      formData.set('department', reportsData.selectedDepartment);
      formData.set('year_level', String(reportsData.selectedYear));
      formData.set('semester', reportUploadDraft.semester);
      formData.set('batch_name', batchName);
      formData.set('section', reportUploadDraft.section);
      formData.set('test_name', reportUploadDraft.test_name);
      formData.set('upload_mode', reportUploadDraft.upload_mode);

      const result = await uploadMarksheet(formData);
      setFlash({
        type: result.parserWarnings.length ? 'warning' : 'success',
        message: result.parserWarnings.length
          ? `${result.message} Parser warnings: ${result.parserWarnings.join(' | ')}`
          : result.message,
      });
      await loadReports(reportsData.selectedDepartment, reportsData.selectedYear);
      await loadTestDetail(result.testId);
      setReportUploadDraft({
        test_name: '',
        semester: '',
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
      const formData = new FormData();
      if (noticeForm.notice_id) formData.set('notice_id', String(noticeForm.notice_id));
      formData.set('notice_title', noticeForm.notice_title);
      formData.set('notice_message_text', noticeForm.notice_message_text);
      if (noticeForm.notice_send_to_all) formData.set('notice_send_to_all', 'on');
      for (const scopeValue of noticeForm.scope_pairs) formData.append('notice_scope_pairs', scopeValue);
      for (const attachmentId of noticeForm.remove_attachment_ids) formData.append('remove_attachment_ids', String(attachmentId));
      for (const file of noticeForm.files) formData.append('notice_attachments', file);

      await saveNotice(formData);
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
    setUserCreateForm({
      name: '',
      email: '',
      password: '',
      confirm_password: '',
      role: nextRole || userAssignableRoles[0] || (currentUser?.role === 'deo' ? 'counselor' : 'counselor'),
      department: '',
      year_level: '1',
      max_students: '30',
      scope_pairs: [],
    });
  }

  async function handleCreateUser(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setUserSaving(true);
    try {
      await createUserAccount({
        ...userCreateForm,
        max_students: Number(userCreateForm.max_students || 30),
        year_level: Number(userCreateForm.year_level || 1),
      });
      setFlash({ type: 'success', message: 'User created successfully.' });
      resetUserCreateForm();
      await refreshUsersOverview();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to create user.' });
    } finally {
      setUserSaving(false);
    }
  }

  function openEditUserModal(user: UserRecord) {
    setUserEditDraft({
      original_email: user.email,
      name: user.name,
      email: user.email,
      password: '',
      role: user.role,
      department: user.department || '',
      year_level: String(user.year_level || 1),
      max_students: String(user.max_students || 30),
      scope_pairs: (user.scopes || []).map((scope) => `${scope.department}::${scope.year_level}`),
    });
  }

  async function handleSaveUserEdit(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!userEditDraft) return;
    setUserSaving(true);
    try {
      await updateUserAccount(userEditDraft.original_email, {
        ...userEditDraft,
        max_students: Number(userEditDraft.max_students || 30),
        year_level: Number(userEditDraft.year_level || 1),
      });
      setUserEditDraft(null);
      setFlash({ type: 'success', message: 'User updated successfully.' });
      await refreshUsersOverview();
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
        await lockUserAccount(userActionTarget.user.email);
      } else if (userActionTarget.kind === 'unlock') {
        await unlockUserAccount(userActionTarget.user.email);
      } else {
        await deleteUserAccount(userActionTarget.user.email);
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
      await refreshUsersOverview();
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
      await refreshUsersOverview();
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
    try {
      const payload = await getActivityScopeReport(filters);
      const pendingCount = (payload.sections || []).reduce(
        (sum, section) => sum + section.rows.filter((row) => Number(row.pending_count || 0) > 0).length,
        0,
      );
      if (!pendingCount) {
        setFlash({ type: 'warning', message: 'No defaulters were found for the selected counselor activity scope.' });
        return;
      }
      const lines = buildActivityCopyLines(payload.sections || [], mode);
      await handleCopyPreparedLines(
        lines,
        'Counselor Activity Defaulters',
        `Copied ${pendingCount} pending counselor entr${pendingCount === 1 ? 'y' : 'ies'} from counselor activity.`,
        String(bootstrap?.appConfig?.activity_copy_as_image || 'false').toLowerCase() === 'true',
      );
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to prepare activity defaulters list.' });
    }
  }

  async function handleDownloadActivityScopePdf(filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
  }) {
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
    await handleCopyPreparedLines(
      buildNoticeCopyLines(pendingRows),
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
      await handleCopyPreparedLines(
        buildNoticeCopyLines(pendingRows),
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
      setFlash({ type: 'success', message: `${email} was logged out.` });
      await loadMonitoringOverview();
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
    try {
      const result = await createDatabaseBackup(databaseBatchName, databaseOverwrite);
      setFlash({ type: 'success', message: result.message });
      setDatabaseOverwrite(false);
      await loadDatabaseOverview();
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to create backup.' });
    }
  }

  async function handleConfirmDatabaseBackupAction(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    if (!databaseBackupAction) return;
    setDatabaseActionLoading(true);
    try {
      if (databaseBackupAction.kind === 'delete') {
        await deleteDatabaseBackup(databaseBackupAction.backupName, databaseActionPassword);
        setFlash({ type: 'success', message: `Deleted backup ${databaseBackupAction.backupName}.` });
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
        window.setTimeout(() => window.location.reload(), 350);
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
    const confirmed = await requestConfirm({
      title: 'Archive Year',
      message: 'Archive the current active year and clear operational data to start fresh? Admin and Principal accounts stay available.',
      confirmLabel: 'Archive And Clear',
      confirmClassName: 'btn btn-danger btn-sm',
      iconClassName: 'fas fa-box-archive',
    });
    if (!confirmed) return;
    setArchiveYearLoading(true);
    try {
      setDatabaseProgress({
        title: 'Archiving Academic Year',
        body: `Creating archive_${archiveYearLabel.replace(/[^0-9A-Za-z_-]/g, '_')}.db and resetting the active workspace. Please wait...`,
      });
      const result = await archiveAcademicYear(archiveYearLabel, clearExamPassword, archiveYearOverwrite);
      if (result.reload) {
        window.setTimeout(() => window.location.reload(), 350);
        return;
      }
      setFlash({ type: 'success', message: 'Academic year archived successfully.' });
      setClearExamPassword('');
      setArchiveYearLabel('');
      setArchiveYearOverwrite(false);
      await loadDatabaseOverview();
    } catch (error) {
      setDatabaseProgress(null);
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to archive academic year.' });
    } finally {
      setArchiveYearLoading(false);
    }
  }

  async function handleSaveConfig(event: FormEvent<HTMLFormElement>) {
    event.preventDefault();
    setConfigSaving(true);
    try {
      const result = await updateConfig(configForm);
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
      setFlash({ type: 'success', message: 'Settings saved successfully.' });
    } catch (error) {
      setFlash({ type: 'error', message: error instanceof Error ? error.message : 'Failed to save settings.' });
    } finally {
      setConfigSaving(false);
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
            <p>Loading Shine rebuild...</p>
          </div>
        </div>
      </main>
    );
  }

  if (!currentUser) {
    return (
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
              <p className="conflict-question">Do you want to logout from the other device and continue here?</p>
              <div className="conflict-buttons">
                <button
                  type="button"
                  className="btn btn-primary"
                  onClick={() => {
                    const fakeEvent = { preventDefault() {} } as FormEvent<HTMLFormElement>;
                    void handleLogin(fakeEvent, true);
                  }}
                >
                  <i className="fas fa-sign-out-alt"></i> Yes, Logout Other Device
                </button>
                <button
                  type="button"
                  className="btn btn-outline"
                  onClick={() => setLoginState((prev) => ({ ...prev, conflict: null }))}
                >
                  <i className="fas fa-times"></i> Cancel
                </button>
              </div>
            </div>
          ) : loginOtpState ? (
            <>
              <form onSubmit={(event) => void handleVerifyLoginOtp(event)} autoComplete="off">
                <div className="form-group">
                  <label className="form-label" htmlFor="loginOtpCode">Login OTP</label>
                  <input
                    type="text"
                    className="form-control"
                    id="loginOtpCode"
                    placeholder="Enter 6-digit OTP"
                    minLength={6}
                    maxLength={6}
                    value={loginState.otp_code}
                    onChange={(event) => setLoginState((prev) => ({ ...prev, otp_code: event.target.value }))}
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
                <i className={`fas ${bootstrap?.authUi?.standardOtpLoginEnabled ? 'fa-paper-plane' : 'fa-sign-in-alt'}`}></i>{' '}
                {loginState.loading
                  ? (bootstrap?.authUi?.standardOtpLoginEnabled ? 'Sending OTP...' : 'Signing In...')
                  : (bootstrap?.authUi?.standardOtpLoginEnabled ? 'Send OTP & Continue' : 'Sign In')}
              </button>

              {bootstrap?.authUi?.googleOauthEnabled ? (
                <>
                  <div style={{ display: 'flex', alignItems: 'center', gap: 10, margin: '16px 0 12px' }}>
                    <div style={{ flex: 1, height: 1, background: 'var(--border)' }}></div>
                    <span style={{ fontSize: '.76rem', color: 'var(--text-dim)', textTransform: 'uppercase', letterSpacing: '.08em' }}>or</span>
                    <div style={{ flex: 1, height: 1, background: 'var(--border)' }}></div>
                  </div>
                  <a
                    href="/auth/google/start"
                    className="btn btn-outline"
                    style={{ width: '100%', display: 'flex', alignItems: 'center', justifyContent: 'center', gap: 8 }}
                  >
                    <i className="fab fa-google"></i> Sign in with Google
                  </a>
                </>
              ) : null}

              {bootstrap?.authUi?.forgotPasswordEnabled ? (
                <div style={{ marginTop: 10, textAlign: 'center' }}>
                  <button
                    type="button"
                    className="btn btn-outline"
                    style={{ width: '100%' }}
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
    );
  }

  return (
    <>
      <aside className={`sidebar ${mobileSidebarOpen ? 'open' : ''}`} id="sidebar">
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
              onClick={() => {
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
              }}
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
              <span className="user-name">{currentUser.name}</span>
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
          <button type="button" className={isTestMode ? 'logout-btn test-mode-btn' : 'logout-btn'} onClick={() => void handleLogout()}>
            <i className={`fas ${isTestMode ? 'fa-door-open' : 'fa-sign-out-alt'}`}></i> {isTestMode ? 'Exit Test Mode' : 'Logout'}
          </button>
        </div>
      </aside>
      {mobileSidebarOpen ? <div className="sidebar-overlay" onClick={() => setMobileSidebarOpen(false)}></div> : null}

      <main className="main-content" id="mainContent">
        <header className="top-header">
          <button className="mobile-toggle" type="button" onClick={() => setMobileSidebarOpen(true)}><i className="fas fa-bars"></i></button>
          <h1 className="page-title">{getPageTitle(activeTab, currentUser)}</h1>
          <div className="header-actions">
            <div className="icon-group">
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

        <div className="content-area">
          {currentUser.role === 'counselor' && activeTab === 'test-database' && counselorSendVerify ? (
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
                <div className="report-sticky-toolbar mb-2">
                  <div className="report-toolbar-balanced">
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => {
                        stopCounselorBatchSend();
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
                      <label className="form-label">WhatsApp Link Mode</label>
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

                <div className="table-wrapper">
                  <table>
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
                              <i className="fab fa-whatsapp"></i> Send to WhatsApp
                            </button>
                          </td>
                        </tr>
                      )) : (
                        <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 18 }}>No students available for this test.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>

                <div style={{ height: 48 }}></div>

                {counselorSendPage.batchSendEnabled && !isMobileUi() ? (
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
                <div className="report-sticky-toolbar mb-2">
                  <div className="report-toolbar-balanced">
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => {
                        stopCounselorNoticeBatchSend();
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
                      <label className="form-label">WhatsApp Link Mode</label>
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
                                <a className="btn btn-outline btn-sm" href={`/notice-files/${attachment.public_token}`} target="_blank" rel="noreferrer">
                                  <i className="fas fa-eye"></i> Open
                                </a>
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
                  <table>
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
                              <i className="fab fa-whatsapp"></i> Send Notice
                            </button>
                          </td>
                        </tr>
                      )) : (
                        <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 18 }}>No students are assigned to your account yet.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>

                <div style={{ height: 48 }}></div>

                {counselorNoticeSendPage.batchSendEnabled && !isMobileUi() ? (
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
                            <button type="button" className="btn btn-primary btn-sm" onClick={() => startCounselorSendFlow(test.id, test.test_name)}>
                              <i className="fas fa-paper-plane"></i> Send Results
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
                  <div className="table-wrapper">
                    <table>
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
                              <button type="button" className="btn btn-primary btn-sm" onClick={() => startCounselorNoticeSendFlow(notice)}>
                                <i className="fas fa-paper-plane"></i> Send Notice
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
            dashboardLoading && !dashboardData ? (
              <div className="card">
                <div className="panel-placeholder">Loading dashboard...</div>
              </div>
            ) : (
              <>
                <div className="d-flex justify-between align-center flex-wrap mb-3" style={{ gap: 12 }}>
                  <h3 className="section-title" style={{ marginBottom: 0 }}>
                    <i className="fas fa-gauge"></i> Dashboard
                  </h3>
                  <button type="button" className="btn btn-outline btn-sm" onClick={() => void loadDashboardOverview()}>
                    <i className="fas fa-rotate"></i> Refresh
                  </button>
                </div>

                {currentUser.role === 'admin' && dashboardData?.admin_status ? (
                  <>
                    <div className="metrics-grid mb-3">
                      <div className="metric-card">
                        <div className="metric-label">Active Sessions</div>
                        <div className="metric-value">{dashboardData.admin_status.sessions.active_sessions}</div>
                        <div className="metric-icon"><i className="fas fa-signal"></i></div>
                      </div>
                      <div className="metric-card">
                        <div className="metric-label">Today Sessions</div>
                        <div className="metric-value">{dashboardData.admin_status.sessions.today_sessions}</div>
                        <div className="metric-icon"><i className="fas fa-calendar-day"></i></div>
                      </div>
                      <div className="metric-card">
                        <div className="metric-label">Backups</div>
                        <div className="metric-value">{dashboardData.admin_status.backup.backup_count + dashboardData.admin_status.backup.auto_backup_count}</div>
                        <div className="metric-icon"><i className="fas fa-database"></i></div>
                      </div>
                      <div className="metric-card">
                        <div className="metric-label">Archives</div>
                        <div className="metric-value">{dashboardData.admin_status.backup.archive_count}</div>
                        <div className="metric-icon"><i className="fas fa-box-archive"></i></div>
                      </div>
                    </div>

                    <div className="dashboard-dual-grid mb-3">
                      <div className="card dashboard-status-card">
                        <div className="card-title"><i className="fas fa-envelope"></i> SMTP Status</div>
                        <div className="dashboard-summary-row">
                          <span className={`badge ${dashboardData.admin_status.smtp.state === 'ready' ? 'badge-success' : 'badge-warning'}`}>{dashboardData.admin_status.smtp.label}</span>
                        </div>
                        <p className="inline-muted" style={{ marginBottom: 10 }}>{dashboardData.admin_status.smtp.detail}</p>
                        <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                          <div><strong>Server:</strong> {dashboardData.admin_status.smtp.config.server || '--'}</div>
                          <div><strong>Username:</strong> {dashboardData.admin_status.smtp.config.username || '--'}</div>
                          <div><strong>From:</strong> {dashboardData.admin_status.smtp.config.email_from || '--'}</div>
                          <div><strong>Port:</strong> {dashboardData.admin_status.smtp.config.port || '--'}</div>
                        </div>
                      </div>

                      <div className="card dashboard-status-card">
                        <div className="card-title"><i className="fas fa-hard-drive"></i> Backup Status</div>
                        <div className="dashboard-summary-row">
                          <span className={`badge ${dashboardData.admin_status.backup.health === 'healthy' ? 'badge-success' : dashboardData.admin_status.backup.health === 'warning' ? 'badge-warning' : 'badge-danger'}`}>{dashboardData.admin_status.backup.label}</span>
                          <span className="badge badge-primary">{dashboardData.admin_status.backup.storage_mode === 'gdrive' ? 'Google Drive' : 'Local'}</span>
                        </div>
                        <p className="inline-muted" style={{ marginBottom: 10 }}>{dashboardData.admin_status.backup.detail}</p>
                        <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                          <div><strong>Auto Backups:</strong> {dashboardData.admin_status.backup.auto_backup_count}</div>
                          <div><strong>Manual Backups:</strong> {dashboardData.admin_status.backup.backup_count}</div>
                          <div><strong>Archives:</strong> {dashboardData.admin_status.backup.archive_count}</div>
                          <div><strong>Periodic Backups:</strong> {dashboardData.admin_status.backup.periodic_enabled ? 'Enabled' : 'Disabled'}</div>
                          <div><strong>Drive Configured:</strong> {dashboardData.admin_status.backup.drive_configured ? 'Yes' : 'No'}</div>
                          <div><strong>Latest Backup:</strong> {dashboardData.admin_status.backup.latest_backup_name ? `${dashboardData.admin_status.backup.latest_backup_name} (${dashboardData.admin_status.backup.latest_backup_modified})` : '--'}</div>
                        </div>
                      </div>
                    </div>

                    <div className="dashboard-dual-grid mb-3">
                      <div className="card dashboard-status-card">
                        <div className="card-title"><i className="fab fa-google"></i> OAuth Status</div>
                        <div className="dashboard-summary-row">
                          <span className={`badge ${dashboardData.admin_status.oauth.enabled && dashboardData.admin_status.oauth.healthy ? 'badge-success' : dashboardData.admin_status.oauth.enabled ? 'badge-warning' : 'badge-muted'}`}>{dashboardData.admin_status.oauth.label}</span>
                        </div>
                        <p className="inline-muted" style={{ marginBottom: 10 }}>{dashboardData.admin_status.oauth.detail}</p>
                        <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                          <div><strong>Allowed Domain:</strong> {dashboardData.admin_status.oauth.allowed_domain || 'Any verified email'}</div>
                          <div><strong>Redirect Base URL:</strong> {dashboardData.admin_status.oauth.redirect_base_url || '--'}</div>
                        </div>
                      </div>

                      <div className="card dashboard-status-card">
                        <div className="card-title"><i className="fas fa-user-shield"></i> Session Health</div>
                        <div className="dashboard-summary-row">
                          <span className="badge badge-success">Peak {dashboardData.admin_status.sessions.peak_concurrent}</span>
                          <span className="badge badge-warning">Forced {dashboardData.admin_status.sessions.forced_logouts}</span>
                        </div>
                        <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                          <div><strong>Active Sessions:</strong> {dashboardData.admin_status.sessions.active_sessions}</div>
                          <div><strong>Today Logins:</strong> {dashboardData.admin_status.sessions.today_sessions}</div>
                          <div><strong>Peak Concurrent:</strong> {dashboardData.admin_status.sessions.peak_concurrent}</div>
                          <div><strong>Forced Logouts:</strong> {dashboardData.admin_status.sessions.forced_logouts}</div>
                        </div>
                      </div>
                    </div>
                  </>
                ) : null}

                <div className="dashboard-dual-grid mb-3">
                  <div className="card dashboard-status-card">
                    <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                      <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-file-lines"></i> Counsellor Completion Status For Marks</div>
                      {currentUser.role === 'hod' ? (
                        <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleCopyActivityDefaulters('scope')}>
                          <i className="fas fa-copy"></i> Copy Defaulters
                        </button>
                      ) : null}
                    </div>
                    <div className="dashboard-summary-row">
                      <span className="badge badge-warning">Pending {dashboardData?.completion_overview.pending_counselors ?? 0}</span>
                      <span className="badge badge-success">Overall {dashboardData?.completion_overview.overall ?? 0}%</span>
                    </div>
                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>Department</th>
                            <th>Completion %</th>
                            <th>Year Breakdown</th>
                          </tr>
                        </thead>
                        <tbody>
                          {(dashboardData?.completion_overview.department_labels || []).length ? dashboardData!.completion_overview.department_labels.map((department, index) => (
                            <tr key={department}>
                              <td><strong>{department}</strong></td>
                              <td>{dashboardData!.completion_overview.department_values[index] ?? 0}%</td>
                              <td style={{ fontSize: '.8rem', color: 'var(--text-dim)' }}>
                                {Object.entries(dashboardData!.completion_overview.department_year_breakdown[department] || {})
                                  .map(([year, value]) => `${formatYearLevel(Number(year))}: ${value}%`)
                                  .join(' | ') || '--'}
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={3} className="text-center text-muted" style={{ padding: 20 }}>No counselor completion data available yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  <div className="card dashboard-status-card">
                    <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                      <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-bullhorn"></i> Notice Completion Status</div>
                      {currentUser.role === 'hod' ? (
                        <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleCopyDashboardNoticeDefaulters()}>
                          <i className="fas fa-copy"></i> Copy Defaulters
                        </button>
                      ) : null}
                    </div>
                    <div className="dashboard-summary-row">
                      <span className="badge badge-warning">Pending {dashboardData?.notice_completion_overview.pending_counselors ?? 0}</span>
                      <span className="badge badge-success">Overall {dashboardData?.notice_completion_overview.overall ?? 0}%</span>
                    </div>
                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>Department</th>
                            <th>Completion %</th>
                            <th>Year Breakdown</th>
                          </tr>
                        </thead>
                        <tbody>
                          {(dashboardData?.notice_completion_overview.department_labels || []).length ? dashboardData!.notice_completion_overview.department_labels.map((department, index) => (
                            <tr key={`notice-${department}`}>
                              <td><strong>{department}</strong></td>
                              <td>{dashboardData!.notice_completion_overview.department_values[index] ?? 0}%</td>
                              <td style={{ fontSize: '.8rem', color: 'var(--text-dim)' }}>
                                {Object.entries(dashboardData!.notice_completion_overview.department_year_breakdown[department] || {})
                                  .map(([year, value]) => `${formatYearLevel(Number(year))}: ${value}%`)
                                  .join(' | ') || '--'}
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={3} className="text-center text-muted" style={{ padding: 20 }}>No notice completion data available yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>
                </div>

                <div className="card">
                  <div className="card-title"><i className="fas fa-trophy"></i> Top Counselors (Completion)</div>
                  <div className="table-wrapper">
                    <table>
                      <thead>
                        <tr>
                          <th>Name</th>
                          <th>Department</th>
                          <th>Students</th>
                          <th>Reached</th>
                          <th>Completion</th>
                        </tr>
                      </thead>
                      <tbody>
                        {(dashboardData?.leaderboard || []).length ? dashboardData!.leaderboard.map((row) => (
                          <tr key={row.email}>
                            <td><strong>{row.name}</strong><br /><span className="inline-muted">{row.email}</span></td>
                            <td>{row.department}</td>
                            <td>{row.student_count}</td>
                            <td>{row.unique_students_messaged}</td>
                            <td><span className="badge badge-success">{row.completion_pct}%</span></td>
                          </tr>
                        )) : (
                          <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 20 }}>No counselor activity yet.</td></tr>
                        )}
                      </tbody>
                    </table>
                  </div>
                </div>
              </>
            )
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

                    {noticesData?.editNotice?.attachments?.length ? (
                      <div className="card mb-2" style={{ padding: 12, background: 'rgba(59,130,246,.06)', border: '1px solid rgba(59,130,246,.2)' }}>
                        <div className="card-title" style={{ fontSize: '.86rem', marginBottom: 10 }}><i className="fas fa-link"></i> Existing Attachments</div>
                        <div style={{ display: 'flex', flexWrap: 'wrap', gap: 10 }}>
                          {noticesData.editNotice.attachments.map((attachment) => (
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
                                <a href={`/notice-files/${attachment.public_token}`} target="_blank" rel="noreferrer" style={{ fontSize: '.75rem' }}>Preview current file</a>
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
                <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                  <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-list"></i> Notice Records</div>
                  <div className="btn-group">
                    <input
                      className="form-control"
                      style={{ minWidth: 260 }}
                      autoComplete="off"
                      data-lpignore="true"
                      data-1p-ignore="true"
                      value={noticeRecordSearch}
                      onChange={(event) => setNoticeRecordSearch(event.target.value)}
                      placeholder="Search notice title, creator or scope"
                    />
                    <select className="form-control" style={{ minWidth: 190 }} value={noticeRecordSort} onChange={(event) => setNoticeRecordSort(event.target.value)}>
                      <option value="latest">Latest First</option>
                      <option value="progress_desc">Highest Progress</option>
                      <option value="attachments_desc">Most Attachments</option>
                      <option value="title_asc">Title A-Z</option>
                      <option value="title_desc">Title Z-A</option>
                    </select>
                  </div>
                </div>
                <div className="inline-muted" style={{ marginBottom: 12 }}>
                  Showing {visibleNoticeRecords.length} notice record{visibleNoticeRecords.length === 1 ? '' : 's'}
                </div>
                <div className="table-wrapper">
                  <table>
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
                                <button type="button" className="btn btn-primary btn-sm" onClick={() => startCounselorNoticeSendFlow(notice)}>
                                  <i className="fas fa-paper-plane"></i> Send Notice
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
                    <div className="btn-group">
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => setNoticeCompletionSortOpen((prev) => !prev)}>
                        <i className="fas fa-arrow-down-wide-short"></i> Sort
                      </button>
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleCopyNoticeDefaulters()}>
                        <i className="fas fa-copy"></i> Copy Defaulters
                      </button>
                    </div>
                  </div>
                  <div className="form-group" style={{ marginBottom: 12 }}>
                    <label className="form-label">Search Counselors</label>
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
                  <div className="table-wrapper">
                    <table>
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
                      <div className="btn-group">
                        <input
                          className="form-control"
                          style={{ minWidth: 260 }}
                          autoComplete="off"
                          data-lpignore="true"
                          data-1p-ignore="true"
                          value={noticeRecordSearch}
                          onChange={(event) => setNoticeRecordSearch(event.target.value)}
                          placeholder="Search notice title, creator or scope"
                        />
                        <select className="form-control" style={{ minWidth: 190 }} value={noticeRecordSort} onChange={(event) => setNoticeRecordSort(event.target.value)}>
                          <option value="latest">Latest First</option>
                          <option value="progress_desc">Highest Progress</option>
                          <option value="attachments_desc">Most Attachments</option>
                          <option value="title_asc">Title A-Z</option>
                          <option value="title_desc">Title Z-A</option>
                        </select>
                      </div>
                    </div>
                    <form className="form-row" style={{ alignItems: 'end', marginBottom: 14 }}>
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
                      <div className="form-group">
                        <label className="form-label">Status</label>
                        <select className="form-control" value={noticeFilters.status} onChange={(event) => setNoticeFilters((prev) => ({ ...prev, status: event.target.value }))}>
                          <option value="">All Status</option>
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
                    <div className="inline-muted" style={{ marginBottom: 12 }}>
                      Showing {visibleNoticeRecords.length} notice record{visibleNoticeRecords.length === 1 ? '' : 's'}
                    </div>
                    <div className="table-wrapper">
                      <table>
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
            <div className="messages-tab-surface">
              <div className="metrics-grid mb-3">
                <div className="metric-card">
                  <div className="metric-label">Total Messages</div>
                  <div className="metric-value">{adminMessagesData?.stats.total ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-envelope"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Today</div>
                  <div className="metric-value">{adminMessagesData?.stats.today ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-calendar-day"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Active Counselors</div>
                  <div className="metric-value">{adminMessagesData?.stats.active_counselors ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-user-group"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Visible Days</div>
                  <div className="metric-value">{adminMessagesData?.messageDays.length ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-calendar-alt"></i></div>
                </div>
              </div>

              <div className="card mb-3">
                <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                  <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-envelope-open-text"></i> Message Logs</div>
                  <button type="button" className="btn btn-outline btn-sm" disabled={adminMessagesLoading} onClick={() => void reloadAdminMessages(adminMessageFilters)}>
                    <i className={`fas ${adminMessagesLoading ? 'fa-spinner fa-spin' : 'fa-rotate'}`}></i> Refresh
                  </button>
                </div>
                <div>
                  <div className="form-row">
                    <div className="form-group">
                      <label className="form-label">Date</label>
                      <SmartDateInput
                        value={adminMessageFilters.day}
                        onChange={(nextValue) => setAdminMessageFilters((prev) => ({
                          ...prev,
                          day: nextValue,
                          year: '',
                          month: '',
                          day_num: '',
                        }))}
                      />
                    </div>
                    <div className="form-group" style={{ minWidth: 240 }}>
                      <label className="form-label">Search Counselor</label>
                      <input
                        className="form-control"
                        autoComplete="off"
                        data-lpignore="true"
                        data-1p-ignore="true"
                        value={adminMessageSearch}
                        onChange={(event) => {
                          const nextValue = event.target.value;
                          setAdminMessageSearch(nextValue);
                          setAdminMessageFilters((prev) => ({ ...prev, q: nextValue.trim() }));
                        }}
                        placeholder="Type counselor name or email"
                      />
                    </div>
                  </div>
                  {filteredAdminMessageSuggestions.length ? (
                    <div className="table-wrapper" style={{ maxHeight: 180, marginBottom: 12 }}>
                      <table>
                        <tbody>
                          {filteredAdminMessageSuggestions.map((suggestion) => (
                            <tr key={`message-suggestion:${suggestion.email}`}>
                              <td>
                                <strong>{suggestion.name || suggestion.email}</strong><br />
                                <span className="inline-muted">{suggestion.email}</span>
                              </td>
                              <td style={{ textAlign: 'right' }}>
                                <button
                                  type="button"
                                  className={`btn btn-sm ${adminMessageFilters.q === (suggestion.name || suggestion.email) ? 'btn-primary' : 'btn-outline'}`}
                                  onClick={() => {
                                    const selected = suggestion.name || suggestion.email;
                                    setAdminMessageSearch(selected);
                                    setAdminMessageFilters((prev) => ({ ...prev, q: selected }));
                                  }}
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
                  {selectedAdminMessageSuggestion ? (
                    <div className="detail-display-panel" style={{ marginBottom: 12 }}>
                      <div className="detail-display-grid">
                        <div>
                          <div className="detail-display-label">Selected Counselor</div>
                          <div className="detail-display-value is-strong">{selectedAdminMessageSuggestion.name || selectedAdminMessageSuggestion.email}</div>
                        </div>
                        <div>
                          <div className="detail-display-label">Email</div>
                          <div className="detail-display-value">{selectedAdminMessageSuggestion.email}</div>
                        </div>
                      </div>
                    </div>
                  ) : null}
                  <div className="btn-group">
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => {
                        const next = { day: '', q: '', year: '', month: '', day_num: '' };
                        setAdminMessageFilters(next);
                        setAdminMessageSearch('');
                        void reloadAdminMessages(next);
                      }}
                    >
                      <i className="fas fa-rotate-left"></i> Reset
                    </button>
                  </div>
                </div>
              </div>

              {(adminMessagesData?.messageDays || []).length ? (
                <div className="card mb-3" style={{ padding: 12 }}>
                  <div className="d-flex flex-wrap" style={{ gap: 8 }}>
                    {adminMessagesData!.messageDays.map((day) => (
                      <button
                        key={day.day}
                        type="button"
                        className={`badge ${adminMessageFilters.day === day.day ? 'badge-primary' : 'badge-info'}`}
                        style={{ border: 'none', cursor: 'pointer' }}
                        onClick={() => {
                          const next = { ...adminMessageFilters, day: day.day };
                          setAdminMessageFilters(next);
                          void reloadAdminMessages(next);
                        }}
                      >
                        {day.day}: {day.total} msg
                      </button>
                    ))}
                  </div>
                </div>
              ) : null}

              <div className="card">
                <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                  <label className="form-check" style={{ margin: 0 }}>
                    <input
                      type="checkbox"
                      checked={!!adminMessagesData?.messages.length && selectedAdminMessageIds.length === adminMessagesData.messages.length}
                      disabled={adminMessagesLoading && !adminMessagesData}
                      onChange={(event) =>
                        setSelectedAdminMessageIds(
                          event.target.checked ? (adminMessagesData?.messages || []).map((message) => message.id) : [],
                        )
                      }
                    />
                    <span>Select all on current view</span>
                  </label>
                  <button type="button" className="btn btn-danger btn-sm" disabled={adminMessagesLoading && !adminMessagesData} onClick={() => void handleDeleteSelectedAdminMessages()}>
                    <i className="fas fa-trash"></i> Delete Selected
                  </button>
                </div>

                <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 8 }}>
                  <span className="inline-muted">
                    Showing {adminMessagesData?.loadedCount ?? adminMessagesData?.messages.length ?? 0} message logs
                    {adminMessagesData?.hasMore ? ' (more available)' : ''}
                  </span>
                  {adminMessagesLoading && adminMessagesData ? (
                    <span className="badge badge-info">Updating...</span>
                  ) : null}
                </div>

                {adminMessagesLoading && !adminMessagesData ? (
                  <div className="panel-placeholder">Loading message logs...</div>
                ) : (adminMessagesData?.groups || []).length ? (
                  adminMessagesData!.groups.map((group) => (
                    <div key={group.day} className="card mb-2" style={{ padding: 12 }}>
                      <div className="d-flex justify-between align-center mb-1" style={{ gap: 8 }}>
                        <strong>Day: {group.day}</strong>
                        <span className="badge badge-info">{group.total} messages</span>
                      </div>
                      <div className="table-wrapper">
                        <table>
                          <thead>
                            <tr>
                              <th style={{ width: 34 }}></th>
                              <th>Time</th>
                              <th>Counselor</th>
                              <th>Student</th>
                              <th>Reg No</th>
                              <th>Mode</th>
                              <th>Status</th>
                              <th>Action</th>
                            </tr>
                          </thead>
                          <tbody>
                            {group.messages.map((message) => (
                              <tr key={message.id}>
                                <td>
                                  <input
                                    type="checkbox"
                                    checked={selectedAdminMessageIdSet.has(message.id)}
                                    onChange={(event) =>
                                      setSelectedAdminMessageIds((prev) =>
                                        event.target.checked ? [...prev, message.id] : prev.filter((id) => id !== message.id),
                                      )
                                    }
                                  />
                                </td>
                                <td style={{ fontSize: '.82rem' }}>{String(message.sent_at || '').slice(11, 19) || '--'}</td>
                                <td>{message.counselor_name || message.counselor_email || '-'}</td>
                                <td>{message.student_name || '-'}</td>
                                <td><strong>{message.reg_no || '-'}</strong></td>
                                <td>
                                  <span className={`badge ${String(message.send_mode || 'app').toLowerCase() === 'web' ? 'badge-info' : 'badge-primary'}`}>
                                    {String(message.send_mode || 'app').toUpperCase()}
                                  </span>
                                </td>
                                <td>
                                  <span className={`badge ${String(message.status || '').toLowerCase() === 'sent' ? 'badge-success' : 'badge-warning'}`}>
                                    {message.status || 'Pending'}
                                  </span>
                                </td>
                                <td>
                                  <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteAdminMessage(message.id)}>
                                    <i className="fas fa-trash"></i>
                                  </button>
                                </td>
                              </tr>
                            ))}
                          </tbody>
                        </table>
                      </div>
                    </div>
                  ))
                ) : (
                  <div className="panel-placeholder">No message activity found for the selected filters.</div>
                )}

                {adminMessagesData?.hasMore ? (
                  <div className="text-center" style={{ marginTop: 14 }}>
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      disabled={adminMessagesLoading}
                      onClick={() => {
                        const nextLimit = adminMessagesLimit + ADMIN_MESSAGES_LIMIT_STEP;
                        void loadAdminMessages(adminMessageFilters, nextLimit);
                      }}
                    >
                      <i className={`fas ${adminMessagesLoading ? 'fa-spinner fa-spin' : 'fa-plus'}`}></i> Load More
                    </button>
                  </div>
                ) : null}
              </div>
            </div>
          ) : ['admin', 'principal', 'deo'].includes(currentUser.role) && activeTab === 'users' ? (
            <>
              <div className="metrics-grid mb-3">
                <div className="metric-card">
                  <div className="metric-label">Total Users</div>
                  <div className="metric-value">{bootstrap?.metrics.totalUsers ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-users"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Counselors</div>
                  <div className="metric-value">{bootstrap?.metrics.counselorCount ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-chalkboard-teacher"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Active Sessions</div>
                  <div className="metric-value">{bootstrap?.metrics.activeSessions ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-signal"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Messages Sent</div>
                  <div className="metric-value">{bootstrap?.metrics.messagesSent ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-paper-plane"></i></div>
                </div>
              </div>

              <div className="card mb-3">
                <h3 className="section-title"><i className="fas fa-list"></i> User List ({filteredUsers.length})</h3>
                <div className="global-action-bar">
                  <div className="form-group" style={{ flex: 1, minWidth: 260 }}>
                    <label className="form-label">Search by Name</label>
                    <input className="form-control" type="text" placeholder="Type name to search..." value={userSearch} onChange={(event) => setUserSearch(event.target.value)} />
                  </div>
                  <div className="form-group" style={{ minWidth: 120, alignSelf: 'end' }}>
                    <button type="button" className="btn btn-outline btn-sm" onClick={() => setUserFilterTrayOpen((prev) => !prev)}>
                      <i className="fas fa-filter"></i> Filters
                    </button>
                  </div>
                  <div className="form-group" style={{ minWidth: 120, alignSelf: 'end' }}>
                    <button type="button" className="btn btn-outline btn-sm" onClick={() => void refreshUsersOverview()}>
                      <i className="fas fa-rotate"></i> Refresh
                    </button>
                  </div>
                </div>

                {userFilterTrayOpen ? (
                  <div className="filter-tray" style={{ marginBottom: 14 }}>
                    <select className="form-control" value={userSortBy} onChange={(event) => setUserSortBy(event.target.value)} style={{ maxWidth: 180 }}>
                      <option value="name_asc">Name A-Z</option>
                      <option value="name_desc">Name Z-A</option>
                      <option value="date_added">Date Added</option>
                      <option value="role">Role</option>
                      <option value="department">Department</option>
                      <option value="year">Year</option>
                    </select>
                    <select className="form-control" value={userFilterDepartment} onChange={(event) => setUserFilterDepartment(event.target.value)} style={{ maxWidth: 180 }}>
                      <option value="">All Departments</option>
                      {userSelectableDepartments.map((department) => (
                        <option key={department.id} value={department.code}>{department.code}</option>
                      ))}
                    </select>
                    <select className="form-control" value={userFilterRole} onChange={(event) => setUserFilterRole(event.target.value)} style={{ maxWidth: 170 }}>
                      <option value="">All Account Types</option>
                      <option value="admin">System Admin</option>
                      <option value="principal">Principal</option>
                      <option value="hod">HoD</option>
                      <option value="deo">DEO</option>
                      <option value="counselor">Counselor</option>
                    </select>
                    <select className="form-control" value={userFilterStatus} onChange={(event) => setUserFilterStatus(event.target.value)} style={{ maxWidth: 150 }}>
                      <option value="">All States</option>
                      <option value="active">Active</option>
                      <option value="inactive">Inactive</option>
                    </select>
                    <select className="form-control" value={userFilterYear} onChange={(event) => setUserFilterYear(event.target.value)} style={{ maxWidth: 140 }}>
                      <option value="">All Years</option>
                      <option value="1">Year 1</option>
                      <option value="2">Year 2</option>
                      <option value="3">Year 3</option>
                      <option value="4">Year 4</option>
                    </select>
                    <select className="form-control" value={userFilterStudentList} onChange={(event) => setUserFilterStudentList(event.target.value)} style={{ maxWidth: 220 }}>
                      <option value="">All Student List Status</option>
                      <option value="with_students">Counselors With Student List</option>
                      <option value="no_students">Counselors With No Student List</option>
                    </select>
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => {
                        setUserFilterDepartment('');
                        setUserFilterRole('');
                        setUserFilterStatus('');
                        setUserFilterYear('');
                        setUserFilterStudentList('');
                        setUserSortBy('name_asc');
                      }}
                    >
                      <i className="fas fa-rotate-left"></i> Reset
                    </button>
                  </div>
                ) : null}

                <div className="table-wrapper">
                  <table id="userTable">
                    <thead>
                      <tr>
                        <th>Name</th>
                        <th>Role</th>
                        <th>Department</th>
                        <th>Year</th>
                        <th>Status</th>
                        <th>Actions</th>
                      </tr>
                    </thead>
                    <tbody>
                      {usersLoading ? (
                        <tr><td colSpan={6} className="text-center text-muted" style={{ padding: 20 }}>Loading users...</td></tr>
                      ) : filteredUsers.length ? filteredUsers.map((row) => (
                        <tr key={row.email}>
                          <td><strong>{row.name}</strong><br /><span className="inline-muted">{row.email}</span></td>
                          <td>
                            <span className={`badge ${getRoleBadgeClass(row.role)}`}>
                              {getRoleOptionLabel(row.role)}
                            </span>
                          </td>
                          <td>
                            {row.role === 'hod' || row.role === 'deo'
                              ? (row.scopes?.length
                                ? row.scopes.length <= 2
                                  ? row.scopes.map((scope) => scope.department).join(', ')
                                  : 'Multiple'
                                : (row.department || '-'))
                              : (row.department || '-')}
                          </td>
                          <td>{row.role === 'counselor' ? formatYearLevel(row.year_level || 1) : '-'}</td>
                          <td>
                            <span className={`badge ${row.is_active && !row.is_locked ? 'badge-success' : 'badge-danger'}`}>
                              {row.is_active && !row.is_locked ? 'Active' : 'Inactive'}
                            </span>
                          </td>
                          <td>
                            <div className="btn-group">
                              {row.can_edit ? (
                                <button type="button" className="btn btn-outline btn-sm" onClick={() => openEditUserModal(row)}>
                                  <i className="fas fa-edit"></i> Edit
                                </button>
                              ) : null}
                              {row.can_manage ? (
                                <>
                                  <button
                                    type="button"
                                    className={`btn btn-sm ${row.is_locked ? 'btn-success' : 'btn-warning'}`}
                                    onClick={() => setUserActionTarget({ kind: row.is_locked ? 'unlock' : 'lock', user: row })}
                                  >
                                    <i className={`fas fa-${row.is_locked ? 'unlock' : 'lock'}`}></i>
                                  </button>
                                  <button type="button" className="btn btn-danger btn-sm" onClick={() => setUserActionTarget({ kind: 'delete', user: row })}>
                                    <i className="fas fa-trash"></i>
                                  </button>
                                </>
                              ) : (
                                <span className="badge badge-info">View Only</span>
                              )}
                            </div>
                          </td>
                        </tr>
                      )) : (
                        <tr><td colSpan={6} className="text-center text-muted" style={{ padding: 20 }}>No users matched the current filter.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>
              </div>

              {currentUser.role !== 'principal' ? (
                <div className="card mb-3">
                  <div className="card-title"><i className="fas fa-user-plus"></i> Register New User</div>
                  <form onSubmit={(event) => void handleCreateUser(event)} autoComplete="off">
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Full Name</label>
                        <input className="form-control" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.name} onChange={(event) => setUserCreateForm((prev) => ({ ...prev, name: event.target.value }))} required placeholder="Dr. John Doe" />
                      </div>
                      <div className="form-group">
                        <label className="form-label">Email</label>
                        <input className="form-control" type="email" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.email} onChange={(event) => setUserCreateForm((prev) => ({ ...prev, email: event.target.value }))} required placeholder="john@rmkcet.ac.in" />
                      </div>
                    </div>
                    <div className="form-row">
                      <div className="form-group">
                        <label className="form-label">Password</label>
                        <input className="form-control" type="password" autoComplete="new-password" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.password} onChange={(event) => setUserCreateForm((prev) => ({ ...prev, password: event.target.value }))} required placeholder="Minimum 6 characters" />
                      </div>
                      <div className="form-group">
                        <label className="form-label">Confirm Password</label>
                        <input className="form-control" type="password" autoComplete="new-password" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.confirm_password} onChange={(event) => setUserCreateForm((prev) => ({ ...prev, confirm_password: event.target.value }))} required placeholder="Re-enter password" />
                      </div>
                    </div>
                    {currentUser.role === 'admin' ? (
                      <div className="form-row">
                        <div className="form-group">
                          <label className="form-label">Role</label>
                          <select
                            className="form-control"
                            value={userCreateForm.role}
                            onChange={(event) => setUserCreateForm((prev) => ({ ...prev, role: event.target.value as Role, scope_pairs: [], department: '', year_level: '1' }))}
                          >
                            {userAssignableRoles.map((role) => (
                              <option key={role} value={role}>{getRoleOptionLabel(role)}</option>
                            ))}
                          </select>
                        </div>
                      </div>
                    ) : null}
                    {(userCreateForm.role === 'hod' || userCreateForm.role === 'deo') ? (
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
                                        checked={userCreateForm.scope_pairs.includes(value)}
                                        onChange={(event) => setUserCreateForm((prev) => ({
                                          ...prev,
                                          scope_pairs: event.target.checked ? [...prev.scope_pairs, value] : prev.scope_pairs.filter((item) => item !== value),
                                        }))}
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
                    {userCreateForm.role === 'counselor' ? (
                      <>
                        <div className="form-row">
                          <div className="form-group">
                            <label className="form-label">Department</label>
                            <select className="form-control" value={userCreateForm.department} onChange={(event) => setUserCreateForm((prev) => ({ ...prev, department: event.target.value }))} required>
                              <option value="">-- Select --</option>
                              {userSelectableDepartments.map((department) => (
                                <option key={department.id} value={department.code}>{department.code} - {department.name}</option>
                              ))}
                            </select>
                          </div>
                          <div className="form-group">
                            <label className="form-label">Year</label>
                            <select className="form-control" value={userCreateForm.year_level} onChange={(event) => setUserCreateForm((prev) => ({ ...prev, year_level: event.target.value }))}>
                              {[1, 2, 3, 4].map((year) => (
                                <option key={year} value={year}>{formatYearLevel(year)}</option>
                              ))}
                            </select>
                          </div>
                        </div>
                        <div className="form-group" style={{ maxWidth: 220 }}>
                          <label className="form-label">Max Students</label>
                          <input className="form-control" type="number" min="1" max="500" value={userCreateForm.max_students} onChange={(event) => setUserCreateForm((prev) => ({ ...prev, max_students: event.target.value }))} />
                        </div>
                      </>
                    ) : null}
                    <button type="submit" className="btn btn-primary" disabled={userSaving}>
                      <i className={`fas ${userSaving ? 'fa-spinner fa-spin' : 'fa-user-plus'}`}></i> Create User
                    </button>
                  </form>
                </div>
              ) : null}

              {currentUser.role !== 'principal' ? (
                <div className="card">
                  <div className="card-title"><i className="fas fa-upload"></i> Bulk Counselor Upload</div>
                  <form onSubmit={(event) => void handleBulkCounselorUpload(event)}>
                    <div className="form-row">
                      <div className="form-group" style={{ maxWidth: 220 }}>
                        <label className="form-label">Year</label>
                        <select className="form-control" value={bulkCounselorForm.year_level} onChange={(event) => setBulkCounselorForm((prev) => ({ ...prev, year_level: event.target.value }))}>
                          {[1, 2, 3, 4].map((year) => (
                            <option key={year} value={year}>{formatYearLevel(year)}</option>
                          ))}
                        </select>
                      </div>
                    </div>
                    <div className="form-group">
                      <label className="form-label">Counselor Excel File</label>
                      <div className="file-input-wrapper">
                        <i className="fas fa-file-excel"></i>
                        <div className="file-text">Choose file</div>
                        <div className="file-name" style={{ display: bulkCounselorForm.file ? 'block' : 'none' }}>{bulkCounselorForm.file?.name || ''}</div>
                        <input
                          key={bulkCounselorUploadKey}
                          type="file"
                          accept=".xlsx,.xls"
                          onChange={(event) => setBulkCounselorForm((prev) => ({ ...prev, file: event.target.files?.[0] || null }))}
                          required
                        />
                      </div>
                    </div>
                    <div className="card" style={{ padding: 12, background: 'rgba(59,130,246,.08)', border: '1px solid rgba(59,130,246,.22)', marginBottom: 12 }}>
                      <div style={{ fontSize: '.84rem', color: 'var(--text-dim)' }}>
                        {String(bootstrap?.appConfig.google_oauth_enabled || 'false').toLowerCase() === 'true'
                          ? 'Google OAuth is enabled. Bulk-uploaded counselor passwords follow the configured sheet/override policy from settings.'
                          : 'Google OAuth is disabled. Bulk-uploaded counselor passwords use the configured non-OAuth fallback from settings, or the password from the sheet when no override is configured.'}
                      </div>
                    </div>
                    <button type="submit" className="btn btn-primary" disabled={bulkCounselorSaving}>
                      <i className={`fas ${bulkCounselorSaving ? 'fa-spinner fa-spin' : 'fa-upload'}`}></i> Run Bulk Upload
                    </button>
                  </form>
                </div>
              ) : null}
            </>
          ) : (['admin', 'principal', 'hod', 'deo'].includes(currentUser.role) && activeTab === 'activity') ? (
            activityLoading && !activityData ? (
              <div className="card">
                <div className="panel-placeholder">Loading counselor activity...</div>
              </div>
            ) : (
              <>
                {activityData?.showDepartmentPicker ? (
                  <div className="mb-3">
                    <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 10 }}>
                      <h3 className="section-title" style={{ margin: 0 }}><i className="fas fa-building"></i> Select Department</h3>
                      <div className="btn-group">
                        <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleCopyActivityDefaulters('scope')}>
                          <i className="fas fa-copy"></i> Copy Defaulters
                        </button>
                        <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleDownloadActivityScopePdf()}>
                          <i className="fas fa-file-pdf"></i> Full Scope PDF
                        </button>
                        <button type="button" className="btn btn-outline btn-sm" onClick={() => void loadActivityOverview()}>
                          <i className="fas fa-rotate"></i> Refresh
                        </button>
                      </div>
                    </div>
                    <div className="metrics-grid selection-grid department-selection-grid">
                      {(activityData?.departments || []).map((department) => (
                        <button
                          key={department.code}
                          type="button"
                          className="metric-card selection-card-button"
                          onClick={() => void loadActivityOverview({ department: department.code })}
                        >
                          <div className="metric-value" style={{ fontSize: '1.6rem' }}>{department.code}</div>
                          <div className="selection-card-subtitle">{department.name}</div>
                        </button>
                      ))}
                    </div>
                  </div>
                ) : null}

                {activityData?.showYearPicker ? (
                  <div className="selection-shell mb-3" style={{ maxWidth: 620 }}>
                    <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
                      <ScopeBreadcrumb
                        icon="fa-layer-group"
                        items={[
                          {
                            label: 'Counsellor Activity',
                            onClick: () => {
                              setActivityFilters({ department: '', year: '', semester: '', test_name: '', q: '', sort: 'pending_first' });
                              void loadActivityOverview();
                            },
                          },
                          { label: activityData.selectedDepartment || 'Department' },
                        ]}
                      />
                      <button
                        type="button"
                        className="btn btn-outline btn-sm"
                        onClick={() => void handleCopyActivityDefaulters('department', { department: activityData.selectedDepartment })}
                      >
                        <i className="fas fa-copy"></i> Copy Defaulters
                      </button>
                    </div>
                    <div className="selection-actions-grid">
                      {(activityData.availableYears || []).map((year) => (
                        <button
                          key={year}
                          type="button"
                          className="btn btn-outline selection-action-button"
                          onClick={() => void loadActivityOverview({ department: activityData.selectedDepartment, year })}
                        >
                          {formatYearLevel(year)}
                        </button>
                      ))}
                    </div>
                  </div>
                ) : null}

                {activityData && !activityData.showDepartmentPicker && !activityData.showYearPicker ? (
                  <div className="card mb-3">
                    <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
                      <ScopeBreadcrumb
                        icon="fa-layer-group"
                        items={[
                          { label: 'Counsellor Activity', onClick: () => void loadActivityOverview() },
                          { label: activityData.selectedDepartment, onClick: () => void loadActivityOverview({ department: activityData.selectedDepartment }) },
                          { label: formatYearLevel(activityData.selectedYear || 1) },
                        ]}
                      />
                      <div className="btn-group">
                        <button
                          type="button"
                          className="btn btn-outline btn-sm"
                          onClick={() => void handleCopyActivityDefaulters('year', {
                            department: activityData.selectedDepartment,
                            year: activityData.selectedYear,
                          })}
                        >
                          <i className="fas fa-copy"></i> Copy Defaulters
                        </button>
                      </div>
                    </div>
                    <div className="test-status-grid">
                      {['1', '2'].map((semester) => (
                        <div key={semester} className="card test-status-panel">
                          <div className="d-flex justify-between align-center" style={{ gap: 10, marginBottom: 12 }}>
                            <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-layer-group"></i> Semester {semester}</div>
                          </div>
                          {['IAT 1', 'IAT 2', 'MODEL EXAM'].map((testName) => {
                            const uploaded = !!activityData.testStatus?.[semester]?.[testName];
                            const active = activityData.selectedSemester === semester && activityData.selectedTestName === testName;
                            return (
                              <div key={`${semester}:${testName}`} className="test-status-row">
                                <button
                                  type="button"
                                  className={`btn ${active ? 'btn-primary' : 'btn-outline'} test-status-button`}
                                  onClick={() => void loadActivityOverview({
                                    department: activityData.selectedDepartment,
                                    year: activityData.selectedYear,
                                    semester,
                                    test_name: testName,
                                  })}
                                >
                                  {testName}
                                </button>
                                <span className={`badge ${uploaded ? 'badge-success' : 'badge-warning'}`}>{uploaded ? 'Uploaded' : 'Upload Pending'}</span>
                              </div>
                            );
                          })}
                        </div>
                      ))}
                    </div>
                  </div>
                ) : null}

                {activityData?.result ? (
                  <>
                    <div className="metrics-grid mb-3">
                      <div className="metric-card">
                        <div className="metric-label">Total Counselors</div>
                        <div className="metric-value">{activityData.result.stats.total_counselors}</div>
                        <div className="metric-icon"><i className="fas fa-users"></i></div>
                      </div>
                      <div className="metric-card">
                        <div className="metric-label">Complete</div>
                        <div className="metric-value">{activityData.result.stats.complete}</div>
                        <div className="metric-icon"><i className="fas fa-circle-check"></i></div>
                      </div>
                      <div className="metric-card">
                        <div className="metric-label">Pending</div>
                        <div className="metric-value">{activityData.result.stats.pending}</div>
                        <div className="metric-icon"><i className="fas fa-clock"></i></div>
                      </div>
                      <div className="metric-card">
                        <div className="metric-label">Avg Completion</div>
                        <div className="metric-value">{activityData.result.stats.avg_completion}%</div>
                        <div className="metric-icon"><i className="fas fa-chart-line"></i></div>
                      </div>
                    </div>

                    <div className="card mb-3">
                      <div className="d-flex align-center flex-wrap" style={{ gap: 8 }}>
                        <input className="form-control" style={{ maxWidth: 280, height: 34, padding: '6px 10px', fontSize: '.82rem' }} value={activityFilters.q} onChange={(event) => setActivityFilters((prev) => ({ ...prev, q: event.target.value }))} placeholder="Search counselor" />
                        <select className="form-control" style={{ maxWidth: 150, height: 34, padding: '6px 10px', fontSize: '.8rem' }} value={activityFilters.sort} onChange={(event) => setActivityFilters((prev) => ({ ...prev, sort: event.target.value }))}>
                          <option value="pending_first">Pending</option>
                          <option value="name_asc">A-Z</option>
                          <option value="name_desc">Z-A</option>
                        </select>
                        <button type="button" className="btn btn-outline btn-sm" style={{ height: 34 }} onClick={() => void loadActivityOverview({
                          department: activityData.selectedDepartment,
                          year: activityData.selectedYear,
                          semester: activityData.selectedSemester,
                          test_name: activityData.selectedTestName,
                        })}>
                          <i className="fas fa-rotate"></i> Refresh
                        </button>
                        <button
                          type="button"
                          className="btn btn-outline btn-sm"
                          style={{ height: 34 }}
                          onClick={() => void handleCopyActivityDefaulters('test', {
                            department: activityData.selectedDepartment,
                            year: activityData.selectedYear,
                            semester: activityData.selectedSemester,
                            test_name: activityData.selectedTestName,
                          })}
                        >
                          <i className="fas fa-copy"></i> Copy Defaulters
                        </button>
                      </div>
                    </div>

                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>Counselor</th>
                            <th>Department</th>
                            <th>Status</th>
                            <th>Completion %</th>
                            <th>Year</th>
                            <th>Students</th>
                            <th>Reached</th>
                            <th>Pending</th>
                            <th>Last Login</th>
                          </tr>
                        </thead>
                        <tbody>
                          {activityDisplayRows.length ? activityDisplayRows.map((row) => (
                            <tr key={row.email}>
                              <td><strong>{row.name}</strong><br /><span className="inline-muted">{row.email}</span></td>
                              <td>{row.department}</td>
                              <td><span className={`badge ${row.work_status === 'Complete' ? 'badge-success' : 'badge-warning'}`}>{row.work_status}</span></td>
                              <td>{row.completion_pct}%</td>
                              <td>{formatYearLevel(row.year_level || 1)}</td>
                              <td>{row.student_count}</td>
                              <td>{row.unique_students_messaged}</td>
                              <td>{row.pending_count}</td>
                              <td style={{ fontSize: '.8rem' }}>{formatDateTime(row.last_login || 'Never')}</td>
                            </tr>
                          )) : (
                            <tr><td colSpan={9} className="text-center text-muted" style={{ padding: 24 }}>No counselor rows found for the current search and sort filters.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </>
                ) : null}
              </>
            )
          ) : (['admin', 'principal'].includes(currentUser.role) && activeTab === 'database') ? (
            <>
              <div className="card mb-3" style={{ maxWidth: 780 }}>
                <div className="card-title"><i className="fas fa-floppy-disk"></i> Create Backup</div>
                <p style={{ fontSize: '.85rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                  Create a full database backup before batch operations.
                </p>
                <form onSubmit={(event) => void handleCreateBackup(event)} className="form-row" style={{ alignItems: 'end' }}>
                  <div className="form-group">
                    <label className="form-label">Batch Label</label>
                    <input className="form-control" value={databaseBatchName} onChange={(event) => setDatabaseBatchName(event.target.value)} placeholder="2025-2026" required />
                  </div>
                  <label className="form-check" style={{ marginBottom: 10 }}>
                    <input type="checkbox" checked={databaseOverwrite} onChange={(event) => setDatabaseOverwrite(event.target.checked)} />
                    <span>Overwrite if same label exists</span>
                  </label>
                  <div className="form-group">
                    <button className="btn btn-primary" type="submit"><i className="fas fa-save"></i> Create Backup</button>
                  </div>
                </form>
              </div>

              {databaseLoading && !databaseData ? (
                <div className="card"><div className="panel-placeholder">Loading database tools...</div></div>
              ) : (
                <>
                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-clock-rotate-left"></i> Automatic Backups (Daily)</div>
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
                          {(databaseData?.autoBackupFiles || []).length ? databaseData!.autoBackupFiles.map((backup) => (
                            <tr key={backup.name}>
                              <td><strong>{backup.name}</strong></td>
                              <td>{backup.size_kb} KB</td>
                              <td>{backup.modified}</td>
                              <td style={{ textAlign: 'right' }}>
                                <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => { setDatabaseBackupAction({ kind: 'restore', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                    <i className="fas fa-rotate-left"></i> Restore
                                  </button>
                                  <button type="button" className="btn btn-danger btn-sm" onClick={() => { setDatabaseBackupAction({ kind: 'delete', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                    <i className="fas fa-trash"></i> Delete
                                  </button>
                                </div>
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
                                <div className="btn-group" style={{ justifyContent: 'flex-end' }}>
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => { setDatabaseBackupAction({ kind: 'restore', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                    <i className="fas fa-rotate-left"></i> Restore
                                  </button>
                                  <button type="button" className="btn btn-danger btn-sm" onClick={() => { setDatabaseBackupAction({ kind: 'delete', backupName: backup.name }); setDatabaseActionPassword(''); }}>
                                    <i className="fas fa-trash"></i> Delete
                                  </button>
                                </div>
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
                            <th>Archive</th>
                            <th>Size</th>
                            <th>Modified</th>
                          </tr>
                        </thead>
                        <tbody>
                          {(databaseData?.archiveFiles || []).length ? databaseData!.archiveFiles.map((archive) => (
                            <tr key={archive.name}>
                              <td><strong>{archive.name}</strong></td>
                              <td>{archive.size_kb} KB</td>
                              <td>{archive.modified}</td>
                            </tr>
                          )) : (
                            <tr><td colSpan={3} className="text-center text-muted" style={{ padding: 20 }}>No year archives available yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  <div className="card" style={{ maxWidth: 860, border: '1px solid rgba(220,38,38,.35)' }}>
                    <div className="card-title"><i className="fas fa-box-archive"></i> Archive Year</div>
                    <p style={{ fontSize: '.85rem', color: 'var(--text-dim)', marginBottom: 12 }}>
                      Creates a year archive in the rebuild archive folder, then clears active operational data while retaining Admin and Principal access.
                    </p>
                    <form onSubmit={(event) => void handleArchiveYear(event)}>
                      <div className="form-row">
                        <div className="form-group">
                          <label className="form-label">Academic Year Range</label>
                          <input
                            className="form-control"
                            value={archiveYearLabel}
                            onChange={(event) => setArchiveYearLabel(event.target.value)}
                            required
                            placeholder="2025_2026"
                          />
                        </div>
                        <div className="form-group">
                          <label className="form-label">Confirm Password</label>
                          <input className="form-control" type="password" value={clearExamPassword} onChange={(event) => setClearExamPassword(event.target.value)} required placeholder="Enter your password" />
                        </div>
                      </div>
                      <label className="form-check" style={{ marginBottom: 12 }}>
                        <input type="checkbox" checked={archiveYearOverwrite} onChange={(event) => setArchiveYearOverwrite(event.target.checked)} />
                        <span>Overwrite if this academic year archive already exists</span>
                      </label>
                      <button className="btn btn-danger" type="submit" disabled={archiveYearLoading}>
                        <i className={`fas ${archiveYearLoading ? 'fa-spinner fa-spin' : 'fa-box-archive'}`}></i> {archiveYearLoading ? 'Archiving...' : 'Clear And Create Active'}
                      </button>
                    </form>
                  </div>
                </>
              )}
            </>
          ) : (currentUser.role === 'admin' && activeTab === 'monitoring') ? (
            <>
              {!monitoringData?.sessionLog.ok ? (
                <div className="card mb-3" style={{ border: '1px solid rgba(245,158,11,.45)' }}>
                  <div className="card-title"><i className="fas fa-triangle-exclamation"></i> Under Maintenance</div>
                  <p style={{ fontSize: '.88rem', color: 'var(--text-dim)' }}>{monitoringData?.sessionLog.message || 'Session monitoring is temporarily unavailable.'}</p>
                </div>
              ) : null}

              <div className="metrics-grid mb-3">
                <div className="metric-card">
                  <div className="metric-label">Active Sessions</div>
                  <div className="metric-value">{monitoringData?.stats.active_sessions ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-signal"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Peak Concurrent</div>
                  <div className="metric-value">{monitoringData?.stats.peak_concurrent ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-chart-line"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Forced Logouts</div>
                  <div className="metric-value">{monitoringData?.stats.forced_logouts ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-power-off"></i></div>
                </div>
                <div className="metric-card">
                  <div className="metric-label">Avg Duration (min)</div>
                  <div className="metric-value">{monitoringData?.stats.avg_duration_minutes ?? 0}</div>
                  <div className="metric-icon"><i className="fas fa-hourglass-half"></i></div>
                </div>
              </div>

              <div className="card mb-3">
                <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                  <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-desktop"></i> Active Sessions ({monitoringData?.sessions.length ?? 0})</div>
                  <div className="btn-group">
                    <button type="button" className="btn btn-outline btn-sm" onClick={() => void loadMonitoringOverview()}>
                      <i className="fas fa-rotate"></i> Refresh
                    </button>
                    <button type="button" className="btn btn-outline btn-sm" onClick={() => void handleCleanupSessions()}>
                      <i className="fas fa-broom"></i> Cleanup
                    </button>
                    <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleLogoutAllUsers()}>
                      <i className="fas fa-power-off"></i> Logout All
                    </button>
                  </div>
                </div>
                <div className="table-wrapper">
                  <table>
                    <thead>
                      <tr>
                        <th>User</th>
                        <th>Role</th>
                        <th>Login</th>
                        <th>Dept</th>
                        <th>Status</th>
                        <th>Last Activity</th>
                        <th>Actions</th>
                      </tr>
                    </thead>
                    <tbody>
                      {monitoringLoading && !monitoringData ? (
                        <tr><td colSpan={6} className="text-center text-muted" style={{ padding: 24 }}>Loading sessions...</td></tr>
                      ) : (monitoringData?.sessions || []).length ? monitoringData!.sessions.map((session) => (
                        <tr key={session.session_id}>
                          <td><strong>{session.name || session.user_email}</strong><br /><span className="inline-muted">{session.user_email}</span></td>
                          <td><span className="badge badge-primary">{session.role || 'N/A'}</span></td>
                          <td><span className={`badge ${String(session.auth_method || 'password').toLowerCase() === 'google' ? 'badge-info' : 'badge-muted'}`}>{String(session.auth_method || 'password').toLowerCase() === 'google' ? 'Google' : 'Password'}</span></td>
                          <td>{session.department || 'N/A'}</td>
                          <td><span className={`badge ${session.status === 'Active' ? 'badge-success' : session.status === 'Idle' ? 'badge-warning' : 'badge-muted'}`}>{session.status}</span></td>
                          <td style={{ fontSize: '.82rem' }}>{session.time_ago || '--'}</td>
                          <td>
                            <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleForceLogout(session.user_email)}>
                              <i className="fas fa-sign-out-alt"></i> Kick
                            </button>
                          </td>
                        </tr>
                      )) : (
                        <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No active sessions.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>
              </div>

              <div className="card">
                <div className="card-title"><i className="fas fa-clock-rotate-left"></i> Session History</div>
                <div className="table-wrapper">
                  <table>
                    <thead>
                      <tr>
                        <th>User</th>
                        <th>Role</th>
                        <th>Login</th>
                        <th>Dept</th>
                        <th>Login Time</th>
                        <th>Last Activity</th>
                        <th>Duration</th>
                        <th>Logout Reason</th>
                      </tr>
                    </thead>
                    <tbody>
                      {(monitoringData?.history || []).length ? monitoringData!.history.map((entry) => (
                        <tr key={`${entry.session_id}:${entry.last_activity}`}>
                          <td><strong>{entry.name || entry.user_email}</strong><br /><span className="inline-muted">{entry.user_email}</span></td>
                          <td>{entry.role || 'N/A'}</td>
                          <td><span className={`badge ${String(entry.auth_method || 'password').toLowerCase() === 'google' ? 'badge-info' : 'badge-muted'}`}>{String(entry.auth_method || 'password').toLowerCase() === 'google' ? 'Google' : 'Password'}</span></td>
                          <td>{entry.department || 'N/A'}</td>
                          <td>{formatDateTime(entry.login_time)}</td>
                          <td>{formatDateTime(entry.last_activity)}</td>
                          <td>{entry.duration || '--'}</td>
                          <td>{entry.logout_reason || '--'}</td>
                        </tr>
                      )) : (
                        <tr><td colSpan={8} className="text-center text-muted" style={{ padding: 24 }}>No session history available yet.</td></tr>
                      )}
                    </tbody>
                  </table>
                </div>
              </div>
            </>
          ) : (currentUser.role === 'admin' && activeTab === 'config') ? (
            configLoading && !configData ? (
              <div className="card"><div className="panel-placeholder">Loading settings...</div></div>
            ) : (
              <>
                <form onSubmit={(event) => void handleSaveConfig(event)}>
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
                        ['tutorial_principal_enabled', 'Principal Tutorial'],
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
                    <label className="form-check">
                      <input type="checkbox" checked={Boolean(configForm.counselor_login_otp_enabled)} disabled={!Boolean(configForm.require_otp_on_login)} onChange={(event) => setConfigForm((prev) => ({ ...prev, counselor_login_otp_enabled: event.target.checked }))} />
                      <span>Require OTP for counselors when login OTP policy is enabled</span>
                    </label>
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
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-hard-drive"></i> Backup Storage Mode</div>
                    <div className="form-row">
                      <div className="form-group" style={{ maxWidth: 280 }}>
                        <label className="form-label">Storage Target</label>
                        <select
                          className="form-control"
                          value={String(configForm.backup_storage_mode || 'local')}
                          onChange={(event) => setConfigForm((prev) => ({ ...prev, backup_storage_mode: event.target.value }))}
                        >
                          <option value="local">Local Rebuild Storage</option>
                          <option value="gdrive">Google Drive</option>
                        </select>
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
                  </div>
                </form>

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
                              <tr key={user.email}>
                                <td>
                                  <strong>{user.name}</strong><br />
                                  <span className="inline-muted">{user.email}</span>
                                </td>
                                <td>{user.role === 'admin' ? 'System Admin' : user.role === 'principal' ? 'Principal' : user.role === 'hod' ? 'HoD' : user.role === 'deo' ? 'DEO' : 'Counselor'}</td>
                                <td style={{ textAlign: 'right' }}>
                                  <button
                                    type="button"
                                    className={`btn btn-sm ${resetPasswordDraft.target_email === user.email ? 'btn-primary' : 'btn-outline'}`}
                                    onClick={() => setResetPasswordDraft((prev) => ({ ...prev, target_email: user.email, new_password: '', confirm_password: '' }))}
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
                              {(configData?.resetUsers || []).find((row) => row.email === resetPasswordDraft.target_email)?.name || resetPasswordDraft.target_email}
                            </div>
                          </div>
                          <div>
                            <div className="detail-display-label">Scope</div>
                            <div className="detail-display-value">
                              {(() => {
                                const selectedRow = (configData?.resetUsers || []).find((row) => row.email === resetPasswordDraft.target_email);
                                if (!selectedRow) return '-';
                                if (selectedRow.role === 'counselor') return `${selectedRow.department || '-'} • ${formatYearLevel(Number(selectedRow.year_level || 1) || 1)}`;
                                return selectedRow.department || getRoleOptionLabel(selectedRow.role);
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
                            <tr key={`preview:${user.email}`}>
                              <td>
                                <strong>{user.name}</strong><br />
                                <span className="inline-muted">{user.email}</span>
                              </td>
                              <td>{getRoleOptionLabel(user.role)}</td>
                              <td style={{ textAlign: 'right' }}>
                                <button
                                  type="button"
                                  className={`btn btn-sm ${previewUserEmail === user.email ? 'btn-primary' : 'btn-outline'}`}
                                  onClick={() => setPreviewUserEmail(user.email)}
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
                          <div className="detail-display-value">{getRoleOptionLabel(previewShellUser.role)}</div>
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
                    <button type="button" className="btn btn-warning" disabled={!previewUserRecord} onClick={() => previewUserRecord ? void handleStartAccountTestMode(previewUserRecord.email) : undefined}>
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
            <>
              {testDetailLoading ? (
                <div className="card">
                  <div className="panel-placeholder">Loading test details...</div>
                </div>
              ) : testDetail ? (
                <div className="report-page-shell">
                  <div className="report-sticky-toolbar report-detail-toolbar mb-2">
                    <div className="report-toolbar-top">
                      <button
                        type="button"
                        className="btn btn-outline btn-sm report-back-btn"
                        onClick={() => setTestDetail(null)}
                      >
                        <i className="fas fa-arrow-left"></i> {currentUser.role === 'counselor' ? 'Back To Test Database' : 'Back To Reports'}
                      </button>
                    </div>
                    <div className="report-toolbar-main">
                      <div className="report-toolbar-cluster report-toolbar-search">
                        <div className="form-group report-toolbar-field">
                          <label className="form-label">Search Students</label>
                          <input
                            className="form-control"
                            placeholder="Search by reg no or student name"
                            value={testDetailSearch}
                            onChange={(event) => setTestDetailSearch(event.target.value)}
                          />
                        </div>
                        <div className="form-group report-toolbar-field report-toolbar-field-sm">
                          <label className="form-label">Sort</label>
                          <select className="form-control" value={testDetailSort} onChange={(event) => setTestDetailSort(event.target.value)}>
                            <option value="reg_asc">Reg No</option>
                            <option value="reg_desc">Reg No (Desc)</option>
                            <option value="name_asc">Name (A-Z)</option>
                            <option value="name_desc">Name (Z-A)</option>
                            <option value="gpa_desc">GPA (High-Low)</option>
                            <option value="gpa_asc">GPA (Low-High)</option>
                            <option value="failed_desc">Failed (High-Low)</option>
                            <option value="failed_asc">Failed (Low-High)</option>
                          </select>
                        </div>
                      </div>
                      <div className="report-toolbar-cluster report-toolbar-end">
                        {!testMarksReadOnly ? (
                          <button className="btn btn-primary report-save-all-btn" type="button" onClick={() => void handleSaveAllMarks()} disabled={savingMarks}>
                            <i className="fas fa-save"></i> {savingMarks ? 'Saving...' : 'Save All Marks'}
                          </button>
                        ) : null}
                        <span className="badge badge-info">{testDetail.meta.test_name || 'Selected Test'}</span>
                      </div>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-pen"></i> Test Metadata</div>
                    <form onSubmit={(event) => void handleSaveMeta(event)}>
                      <div className="form-row">
                        <div className="form-group">
                          <label className="form-label">Test Name</label>
                          <select
                            className="form-control"
                            value={testMetaDraft.test_name}
                            disabled={testMetaReadOnly}
                            onChange={(event) => setTestMetaDraft((prev) => ({ ...prev, test_name: event.target.value }))}
                          >
                            <option value="IAT 1">IAT 1</option>
                            <option value="IAT 2">IAT 2</option>
                            <option value="MODEL EXAM">MODEL EXAM</option>
                          </select>
                        </div>
                        <div className="form-group">
                          <label className="form-label">Semester</label>
                          <input
                            type="text"
                            className="form-control"
                            value={testMetaDraft.semester}
                            readOnly={testMetaReadOnly}
                            onChange={(event) => setTestMetaDraft((prev) => ({ ...prev, semester: event.target.value }))}
                          />
                        </div>
                        <div className="form-group">
                          <label className="form-label">Section</label>
                          <input
                            type="text"
                            className="form-control"
                            value={testMetaDraft.section}
                            readOnly={testMetaReadOnly}
                            placeholder="e.g. A, B, C"
                            onChange={(event) => setTestMetaDraft((prev) => ({ ...prev, section: event.target.value }))}
                          />
                        </div>
                        <div className="form-group">
                          <label className="form-label">Batch</label>
                          <input
                            type="text"
                            className="form-control"
                            value={testMetaDraft.batch_name}
                            readOnly={testMetaReadOnly}
                            onChange={(event) => setTestMetaDraft((prev) => ({ ...prev, batch_name: event.target.value }))}
                          />
                        </div>
                        <div className="form-group">
                          <label className="form-label">Department</label>
                          <input className="form-control" value={testDetail.meta.department || '-'} readOnly />
                        </div>
                        <div className="form-group">
                          <label className="form-label">Year</label>
                          <input className="form-control" value={formatYearLevel(testDetail.meta.year_level || 1)} readOnly />
                        </div>
                      </div>
                      {!testMetaReadOnly ? (
                        <button className="btn btn-primary" type="submit" disabled={savingMeta}>
                          <i className="fas fa-save"></i> {savingMeta ? 'Saving...' : 'Save Metadata'}
                        </button>
                      ) : null}
                    </form>
                  </div>

                  <div className="card">
                    <div className="card-title">
                      <span><i className="fas fa-table"></i> Student Marks</span>
                    </div>
                    <div className="table-wrapper report-marks-scroll">
                      <table className="report-marks-table">
                        <thead>
                          <tr>
                            <th>Reg No</th>
                            <th>Student Name</th>
                            {testDetail.subjects.map((subject) => (
                              <th key={subject}>{subject}</th>
                            ))}
                            <th>GPA</th>
                            <th className="summary-col-failed">Failed</th>
                            {!testMarksReadOnly ? <th>Action</th> : null}
                          </tr>
                        </thead>
                        <tbody>
                          {visibleTestDetailStudents.length ? visibleTestDetailStudents.map((student: ReportStudentRow) => (
                            <tr key={student.reg_no}>
                              <td><strong>{student.reg_no}</strong></td>
                              <td>{student.student_name || '-'}</td>
                              {testDetail.subjects.map((subject) => (
                                <td key={`${student.reg_no}:${subject}`}>
                                  {testMarksReadOnly ? (
                                    student.marks[subject] || ''
                                  ) : (
                                    <input
                                      className="form-control"
                                      value={student.marks[subject] || ''}
                                      style={{ minWidth: 80 }}
                                      onChange={(event) => updateLocalMark(student.reg_no, subject, event.target.value)}
                                    />
                                  )}
                                </td>
                              ))}
                              <td>{readSummaryMetric(student.marks, ['GPA', 'gpa', 'CGPA', 'cgpa'])}</td>
                              <td className="summary-col-failed">{readSummaryMetric(student.marks, ['No. of subjects failed', 'noofsubjectsfailed', 'failedsubjects'])}</td>
                              {!testMarksReadOnly ? (
                                <td>
                                  <button className="btn btn-sm btn-primary" type="button" onClick={() => void handleSaveRowMarks(student.reg_no)}>
                                    <i className="fas fa-save"></i>
                                  </button>
                                </td>
                              ) : null}
                            </tr>
                          )) : (
                            <tr>
                              <td colSpan={testDetail.subjects.length + (testMarksReadOnly ? 4 : 5)} className="text-center text-muted" style={{ padding: 22 }}>
                                No students match the current search and sort filters.
                              </td>
                            </tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>
                </div>
              ) : currentUser.role === 'counselor' ? (
                <>
                  <h3 className="section-title"><i className="fas fa-file-lines"></i> Reports</h3>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-database"></i> Semester 1</div>
                    <div className="table-wrapper">
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
                          {counselorTestsLoading ? (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading tests...</td></tr>
                          ) : counselorTestsBySemester.sem1.length ? counselorTestsBySemester.sem1.map((test) => (
                            <tr key={test.id}>
                              <td><strong>{test.test_name}</strong></td>
                              <td>{formatYearLevel(test.year_level || (currentUser.year_level || 1))}</td>
                              <td>{test.batch_name || '-'}</td>
                              <td>{test.semester || '-'}</td>
                              <td><span className="badge badge-info">{test.student_count}</span></td>
                              <td>
                                {test.is_blocked ? (
                                  <span className="badge badge-danger">Blocked By Admin</span>
                                ) : (test.generated_count || 0) > 0 ? (
                                  <span className="badge badge-success">Uploaded</span>
                                ) : (
                                  <span className="badge badge-warning">Upload Pending</span>
                                )}
                              </td>
                              <td>
                                <div className="btn-group">
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => void loadTestDetail(test.id)} disabled={Boolean(test.is_blocked)}>
                                    <i className="fas fa-eye"></i> View/Edit
                                  </button>
                                  <button type="button" className="btn btn-primary btn-sm" onClick={() => startCounselorSendFlow(test.id, test.test_name)} disabled={Boolean(test.is_blocked)}>
                                    <i className="fas fa-paper-plane"></i> Send Results
                                  </button>
                                </div>
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No semester 1 tests mapped yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-database"></i> Semester 2</div>
                    <div className="table-wrapper">
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
                          {counselorTestsLoading ? (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading tests...</td></tr>
                          ) : counselorTestsBySemester.sem2.length ? counselorTestsBySemester.sem2.map((test) => (
                            <tr key={test.id}>
                              <td><strong>{test.test_name}</strong></td>
                              <td>{formatYearLevel(test.year_level || (currentUser.year_level || 1))}</td>
                              <td>{test.batch_name || '-'}</td>
                              <td>{test.semester || '-'}</td>
                              <td><span className="badge badge-info">{test.student_count}</span></td>
                              <td>
                                {test.is_blocked ? (
                                  <span className="badge badge-danger">Blocked By Admin</span>
                                ) : (test.generated_count || 0) > 0 ? (
                                  <span className="badge badge-success">Uploaded</span>
                                ) : (
                                  <span className="badge badge-warning">Upload Pending</span>
                                )}
                              </td>
                              <td>
                                <div className="btn-group">
                                  <button type="button" className="btn btn-outline btn-sm" onClick={() => void loadTestDetail(test.id)} disabled={Boolean(test.is_blocked)}>
                                    <i className="fas fa-eye"></i> View/Edit
                                  </button>
                                  <button type="button" className="btn btn-primary btn-sm" onClick={() => startCounselorSendFlow(test.id, test.test_name)} disabled={Boolean(test.is_blocked)}>
                                    <i className="fas fa-paper-plane"></i> Send Results
                                  </button>
                                </div>
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No semester 2 tests mapped yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>
                </>
              ) : !reportsData?.selectedDepartment ? (
                <div className="mb-3">
                  <h3 className="section-title"><i className="fas fa-building"></i> Select Department</h3>
                  <div className="metrics-grid selection-grid department-selection-grid">
                    {(reportsData?.departments || []).map((department) => (
                      <button
                        key={department.id}
                        type="button"
                        className="metric-card selection-card-button"
                        onClick={() => void loadReports(department.code)}
                      >
                        <div className="metric-value" style={{ fontSize: '1.6rem' }}>{department.code}</div>
                        <div className="selection-card-subtitle">{department.name}</div>
                      </button>
                    ))}
                    {!reportsLoading && !(reportsData?.departments || []).length ? (
                      <div className="card" style={{ padding: 16, fontSize: '.9rem', color: 'var(--text-dim)' }}>No departments available for your scope.</div>
                    ) : null}
                  </div>
                </div>
              ) : !reportsData.selectedYear ? (
                <div className="selection-shell mb-3" style={{ maxWidth: 620 }}>
                  <ScopeBreadcrumb
                    icon="fa-file-lines"
                    items={[
                      { label: 'Reports', onClick: () => void loadReports() },
                      { label: reportsData.selectedDepartment },
                    ]}
                  />
                  <div className="selection-actions-grid">
                    {reportsData.availableYears.map((year) => (
                      <button
                        key={year}
                        type="button"
                        className="btn btn-outline selection-action-button"
                        onClick={() => void loadReports(reportsData.selectedDepartment, year)}
                      >
                        {formatYearLevel(year)}
                      </button>
                    ))}
                    {!reportsData.availableYears.length ? (
                      <div className="card" style={{ padding: 12, fontSize: '.86rem', color: 'var(--text-dim)' }}>No years allocated for this department.</div>
                    ) : null}
                  </div>
                </div>
              ) : (
                <>
                  <div className="d-flex align-center justify-between flex-wrap mb-2" style={{ gap: 12 }}>
                    <ScopeBreadcrumb
                      icon="fa-file-lines"
                      items={[
                        { label: 'Reports', onClick: () => void loadReports() },
                        { label: reportsData.selectedDepartment, onClick: () => void loadReports(reportsData.selectedDepartment) },
                        { label: formatYearLevel(reportsData.selectedYear) },
                      ]}
                    />
                  </div>

                  {(currentUser.role === 'admin' || currentUser.role === 'deo') ? (
                    <div className="card mb-3">
                      <div className="card-title"><i className="fas fa-file-upload"></i> Upload Marksheet</div>
                      <form onSubmit={(event) => void handleUploadReport(event)}>
                        <div className="form-row">
                          <div className="form-group">
                            <label className="form-label">Department</label>
                            <input className="form-control" value={reportsData.selectedDepartment} readOnly />
                          </div>
                          <div className="form-group">
                            <label className="form-label">Year</label>
                            <input className="form-control" value={formatYearLevel(reportsData.selectedYear)} readOnly />
                          </div>
                        </div>
                        <div className="form-row">
                          <div className="form-group">
                            <label className="form-label">Test Name</label>
                            <select
                              className="form-control"
                              value={reportUploadDraft.test_name}
                              onChange={(event) => setReportUploadDraft((prev) => ({ ...prev, test_name: event.target.value }))}
                              required
                            >
                              <option value="">-- Select Test --</option>
                              <option value="IAT 1">IAT 1</option>
                              <option value="IAT 2">IAT 2</option>
                              <option value="MODEL EXAM">MODEL EXAM</option>
                            </select>
                          </div>
                          <div className="form-group">
                            <label className="form-label">Semester</label>
                            <select
                              className="form-control"
                              value={reportUploadDraft.semester}
                              onChange={(event) => setReportUploadDraft((prev) => ({ ...prev, semester: event.target.value }))}
                              required
                            >
                              <option value="1">1</option>
                              <option value="2">2</option>
                            </select>
                          </div>
                        </div>
                        <div className="form-group" style={{ maxWidth: 380 }}>
                          <label className="form-label">Upload Mode</label>
                          <select
                            className="form-control"
                            value={reportUploadDraft.upload_mode}
                            onChange={(event) => setReportUploadDraft((prev) => ({ ...prev, upload_mode: event.target.value }))}
                          >
                            <option value="new">Keep as New Test</option>
                            <option value="replace">Replace Existing Matching Test</option>
                          </select>
                        </div>
                        <div className="form-group">
                          <label className="form-label">Marksheet File</label>
                          <div className="file-input-wrapper">
                            <i className="fas fa-file-excel"></i>
                            <div className="file-text">Upload Excel marksheet (.xlsx, .xls)</div>
                            <div className="file-name" style={{ display: reportUploadDraft.file ? 'block' : 'none' }}>{reportUploadDraft.file?.name || ''}</div>
                            <input
                              key={reportUploadInputKey}
                              type="file"
                              accept=".xlsx,.xls"
                              onChange={(event) =>
                                setReportUploadDraft((prev) => ({
                                  ...prev,
                                  file: event.target.files?.[0] || null,
                                  batch_name: getDefaultBatchNameForYearLevel(reportsData.selectedYear ?? 1, bootstrap?.appConfig || null),
                                  section: '',
                                }))
                              }
                              required
                            />
                          </div>
                        </div>
                        <button className="btn btn-primary" type="submit" disabled={uploadingReport}>
                          <i className={`fas ${uploadingReport ? 'fa-spinner fa-spin' : 'fa-upload'}`}></i> {uploadingReport ? 'Uploading...' : 'Upload Marksheet'}
                        </button>
                      </form>
                    </div>
                  ) : null}

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-database"></i> {reportsData.selectedDepartment} - {formatYearLevel(reportsData.selectedYear)} - Semester 1</div>
                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>Test Name</th>
                            <th>Batch</th>
                            <th>Semester</th>
                            <th>Uploaded By</th>
                            <th>Students</th>
                            <th>Uploaded At</th>
                            <th>Actions</th>
                          </tr>
                        </thead>
                        <tbody>
                          {reportsLoading ? (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading reports...</td></tr>
                          ) : reportTestsBySemester.sem1.length ? reportTestsBySemester.sem1.map((test) => (
                            <tr key={test.id}>
                              <td><strong>{test.test_name || `Test #${test.id}`}</strong></td>
                              <td>{test.batch_name || '-'}</td>
                              <td>{test.semester || '-'}</td>
                              <td><span style={{ fontSize: '.85rem' }}>{test.uploaded_by_name || test.uploaded_by || '-'}</span></td>
                              <td><span className="badge badge-info">{test.student_count || 0}</span></td>
                              <td style={{ fontSize: '.82rem' }}>{(test.uploaded_at || '').slice(0, 16)}</td>
                              <td>
                                <div className="btn-group">
                                  <button
                                    type="button"
                                    className="btn btn-outline btn-sm"
                                    onClick={() => void loadTestDetail(test.id)}
                                  >
                                    <i className={`fas ${currentUser.role === 'principal' ? 'fa-eye' : 'fa-pen'}`}></i> {currentUser.role === 'principal' ? 'View' : 'Edit/View'}
                                  </button>
                                  {currentUser.role !== 'principal' ? (
                                    <>
                                      <button type="button" className={`btn ${test.is_blocked ? 'btn-success' : 'btn-warning'} btn-sm`} onClick={() => void handleToggleTestBlock(test)}>
                                        <i className={`fas ${test.is_blocked ? 'fa-lock-open' : 'fa-lock'}`}></i>
                                      </button>
                                      <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteTest(test)}>
                                        <i className="fas fa-trash"></i>
                                      </button>
                                    </>
                                  ) : null}
                                </div>
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No semester 1 tests uploaded yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>

                  <div className="card mb-3">
                    <div className="card-title"><i className="fas fa-database"></i> {reportsData.selectedDepartment} - {formatYearLevel(reportsData.selectedYear)} - Semester 2</div>
                    <div className="table-wrapper">
                      <table>
                        <thead>
                          <tr>
                            <th>Test Name</th>
                            <th>Batch</th>
                            <th>Semester</th>
                            <th>Uploaded By</th>
                            <th>Students</th>
                            <th>Uploaded At</th>
                            <th>Actions</th>
                          </tr>
                        </thead>
                        <tbody>
                          {reportsLoading ? (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading reports...</td></tr>
                          ) : reportTestsBySemester.sem2.length ? reportTestsBySemester.sem2.map((test) => (
                            <tr key={test.id}>
                              <td><strong>{test.test_name || `Test #${test.id}`}</strong></td>
                              <td>{test.batch_name || '-'}</td>
                              <td>{test.semester || '-'}</td>
                              <td><span style={{ fontSize: '.85rem' }}>{test.uploaded_by_name || test.uploaded_by || '-'}</span></td>
                              <td><span className="badge badge-info">{test.student_count || 0}</span></td>
                              <td style={{ fontSize: '.82rem' }}>{(test.uploaded_at || '').slice(0, 16)}</td>
                              <td>
                                <div className="btn-group">
                                  <button
                                    type="button"
                                    className="btn btn-outline btn-sm"
                                    onClick={() => void loadTestDetail(test.id)}
                                  >
                                    <i className={`fas ${currentUser.role === 'principal' ? 'fa-eye' : 'fa-pen'}`}></i> {currentUser.role === 'principal' ? 'View' : 'Edit/View'}
                                  </button>
                                  {currentUser.role !== 'principal' ? (
                                    <>
                                      <button type="button" className={`btn ${test.is_blocked ? 'btn-success' : 'btn-warning'} btn-sm`} onClick={() => void handleToggleTestBlock(test)}>
                                        <i className={`fas ${test.is_blocked ? 'fa-lock-open' : 'fa-lock'}`}></i>
                                      </button>
                                      <button type="button" className="btn btn-danger btn-sm" onClick={() => void handleDeleteTest(test)}>
                                        <i className="fas fa-trash"></i>
                                      </button>
                                    </>
                                  ) : null}
                                </div>
                              </td>
                            </tr>
                          )) : (
                            <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No semester 2 tests uploaded yet.</td></tr>
                          )}
                        </tbody>
                      </table>
                    </div>
                  </div>
                </>
              )}
            </>
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

        <footer className="global-footer">
          <div className="global-footer-inner">
            <div className="global-footer-left">
              <img src="/assets/banner.png" alt="RMKCET Banner" className="global-footer-banner-image" />
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
              <a className="global-footer-link global-footer-btn" href="/api/footer/credits">Credits</a>
              {currentUser.role !== 'admin' ? (
                <a className="global-footer-link global-footer-btn" href={getFooterSupportHref(currentUser)} target="_blank" rel="noreferrer">Support</a>
              ) : null}
            </div>
          </div>
        </footer>
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
                    className="form-control"
                    autoComplete="off"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={forgotPasswordState.otp_code}
                    onChange={(event) => setForgotPasswordState((prev) => ({ ...prev, otp_code: event.target.value }))}
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
                    className="form-control"
                    autoComplete="off"
                    data-lpignore="true"
                    data-1p-ignore="true"
                    value={selfPasswordDraft.otp_code}
                    onChange={(event) => setSelfPasswordDraft((prev) => ({ ...prev, otp_code: event.target.value }))}
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
                    <select className="form-control" value={userEditDraft.role} onChange={(event) => setUserEditDraft((prev) => prev ? { ...prev, role: event.target.value as Role, scope_pairs: [], department: '', year_level: '1' } : prev)}>
                      {userAssignableRoles.map((role) => (
                        <option key={role} value={role}>{getRoleOptionLabel(role)}</option>
                      ))}
                    </select>
                  </div>
                ) : null}
              </div>
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
                      <span className="badge badge-success">{typeof users.find((item) => item.email === userEditDraft.original_email)?.student_count === 'number' ? users.find((item) => item.email === userEditDraft.original_email)?.student_count : 0} students</span>
                    </div>
                    <div className="btn-group">
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => {
                        const targetUser = users.find((item) => item.email === userEditDraft.original_email);
                        if (targetUser) void loadCounselorStudents(targetUser);
                      }}>
                        <i className="fas fa-pen"></i> Edit/View All
                      </button>
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => {
                        const targetUser = users.find((item) => item.email === userEditDraft.original_email);
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

      {databaseBackupAction ? (
        <div className="modal-overlay open" onClick={() => { if (!databaseActionLoading) setDatabaseBackupAction(null); }}>
          <div className="modal" style={{ maxWidth: 460 }} onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <h3><i className="fas fa-triangle-exclamation"></i> {databaseBackupAction.kind === 'restore' ? 'Restore Backup' : 'Delete Backup'}</h3>
              <button className="modal-close" type="button" onClick={() => setDatabaseBackupAction(null)} disabled={databaseActionLoading}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <p style={{ fontSize: '.9rem', color: 'var(--text-dim)', marginBottom: 12 }}>
              {databaseBackupAction.kind === 'restore'
                ? `Restore backup ${databaseBackupAction.backupName}? This logs out all users and replaces the current database.`
                : `Delete backup ${databaseBackupAction.backupName}? This cannot be undone.`}
            </p>
            <form onSubmit={(event) => void handleConfirmDatabaseBackupAction(event)}>
              <div className="form-group">
                <label className="form-label">Confirm Password</label>
                <input className="form-control" type="password" value={databaseActionPassword} onChange={(event) => setDatabaseActionPassword(event.target.value)} required placeholder="Enter your password" />
              </div>
              <div className="btn-group" style={{ justifyContent: 'flex-end', gap: 8 }}>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => setDatabaseBackupAction(null)} disabled={databaseActionLoading}>Cancel</button>
                <button type="submit" className={`btn btn-sm ${databaseBackupAction.kind === 'restore' ? 'btn-outline' : 'btn-danger'}`} disabled={databaseActionLoading}>
                  <i className={`fas ${databaseActionLoading ? 'fa-spinner fa-spin' : databaseBackupAction.kind === 'restore' ? 'fa-rotate-left' : 'fa-trash'}`}></i>
                  {databaseActionLoading ? 'Working...' : databaseBackupAction.kind === 'restore' ? 'Restore' : 'Delete'}
                </button>
              </div>
            </form>
          </div>
        </div>
      ) : null}
    </>
  );
}

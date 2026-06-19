import type {
  DashboardOverviewPayload,
  ActivityOverviewPayload,
  ActivityScopeReportPayload,
  AdminMessagesOverviewPayload,
  BootstrapPayload,
  ConfigOverviewPayload,
  CounselorNoticeSendPagePayload,
  CounselorMessageRecord,
  CounselorMessageStats,
  CounselorOverviewPayload,
  CounselorStudentRecord,
  CounselorSendPagePayload,
  CounselorVisibleTestRecord,
  DatabaseOverviewPayload,
  DepartmentRecord,
  MonitoringOverviewPayload,
  NoticesOverviewPayload,
  CdpOverviewPayload,
  ReportsOverviewPayload,
  ReportUploadPayload,
  ServerConsolePayload,
  SendSinglePreparedPayload,
  SubjectsOverviewPayload,
  TestDetailPayload,
  UserRecord,
  UsersOverviewPayload,
} from './types';
import {
  clearStoredAuthState,
  redirectToAppRoot,
  reloadCurrentApp,
  resolveDirectServerUrl,
} from './runtime';
import { recordPerformanceEvent } from './performance';

function recordApiServerTiming(response: Response) {
  const serverTiming = response.headers.get('Server-Timing') || '';
  const appMatch = /app;dur=([0-9.]+)/i.exec(serverTiming);
  if (!appMatch) return;
  const durationMs = Number(appMatch[1]);
  if (!Number.isFinite(durationMs)) return;
  let path = response.url;
  try {
    path = new URL(response.url).pathname;
  } catch {
    // Keep the raw response URL when URL parsing is unavailable.
  }
  recordPerformanceEvent({
    area: 'server-api',
    name: path,
    durationMs,
    status: response.ok ? 'ok' : 'error',
    meta: {
      status: response.status,
      method: 'response',
    },
  });
}

async function parseJson<T>(response: Response, options?: { redirectOn401?: boolean }): Promise<T> {
  recordApiServerTiming(response);
  const raw = await response.text();
  let payload: any = null;
  if (raw) {
    try {
      payload = JSON.parse(raw);
    } catch {
      const fallbackMessage = response.ok
        ? 'Server returned an invalid response.'
        : (/^\s*</.test(raw) ? `Server error (${response.status}). Please try again.` : raw.slice(0, 220));
      if (response.status === 401 && options?.redirectOn401 !== false && typeof window !== 'undefined') {
        clearStoredAuthState();
        reloadCurrentApp();
      }
      throw new Error(fallbackMessage);
    }
  }
  if (!response.ok) {
    const message = (payload && (payload.error || payload.message)) || 'Request failed';
    if (response.status === 401 && options?.redirectOn401 !== false && typeof window !== 'undefined') {
      clearStoredAuthState();
      redirectToAppRoot();
    }
    const error = new Error(message) as Error & { status?: number; payload?: unknown };
    error.status = response.status;
    error.payload = payload;
    throw error;
  }
  return payload as T;
}

export async function getBootstrap(): Promise<BootstrapPayload> {
  const response = await fetch('/api/bootstrap', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<BootstrapPayload>(response);
}

export async function login(identifier: string, password: string, forceLogout = false) {
  const response = await fetch('/api/auth/login', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ identifier, password, forceLogout }),
  });
  const payload = await response.json();
  if (!response.ok) {
    const error = (payload && (payload.error || payload.message)) || 'Login failed';
    const ext = new Error(error) as Error & { payload?: unknown; status?: number };
    ext.payload = payload;
    ext.status = response.status;
    throw ext;
  }
  return payload;
}

export async function verifyLoginOtp(otp_code: string) {
  const response = await fetch('/api/auth/login/verify-otp', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ otp_code }),
  });
  return parseJson<{
    success: true;
    requiresRoleSelection?: boolean;
    authMethod?: 'password' | 'google';
    loginEmail?: string;
    options?: Array<{
      accountEmail: string;
      role: string;
      name: string;
      designation?: string;
      department: string;
      year_level: number;
    }>;
  }>(response, { redirectOn401: false });
}

export async function getLoginRoleSelection() {
  const response = await fetch('/api/auth/login/role-selection', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{
    success: true;
    requiresRoleSelection: true;
    authMethod: 'password' | 'google';
    loginEmail: string;
    options: Array<{
      accountEmail: string;
      role: string;
      name: string;
      designation?: string;
      department: string;
      year_level: number;
    }>;
  }>(response, { redirectOn401: false });
}

export async function selectLoginRole(account_email: string, forceLogout = false) {
  const response = await fetch('/api/auth/login/select-role', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ account_email, forceLogout }),
  });
  return parseJson<any>(response, { redirectOn401: false });
}

export async function switchSessionRole(account_email: string) {
  const response = await fetch('/api/auth/switch-role', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ account_email }),
  });
  return parseJson<{ success: true }>(response);
}

export async function getSessionRoleSwitchOptions() {
  const response = await fetch('/api/auth/switch-role/options', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{
    success: true;
    options: Array<{
      accountEmail: string;
      role: string;
      name: string;
      designation?: string;
      department: string;
      year_level: number;
    }>;
  }>(response);
}

export async function resolveGoogleLoginConflict() {
  const response = await fetch('/api/auth/google/resolve-conflict', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function resendLoginOtp() {
  const response = await fetch('/api/auth/login/resend-otp', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; maskedEmail: string }>(response);
}

export async function cancelLoginOtp() {
  const response = await fetch('/api/auth/login/cancel-otp', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function logout() {
  const response = await fetch('/api/auth/logout', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function requestPasswordReset(identifier: string) {
  const response = await fetch('/api/auth/password-reset/request', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ identifier }),
  });
  return parseJson<{ success: true; maskedEmail: string }>(response);
}

export async function verifyPasswordResetOtp(otp_code: string) {
  const response = await fetch('/api/auth/password-reset/verify-otp', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ otp_code }),
  });
  return parseJson<{ success: true; maskedEmail: string }>(response, { redirectOn401: false });
}

export async function completePasswordReset(payload: { new_password: string; confirm_password: string }) {
  const response = await fetch('/api/auth/password-reset/complete', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function sendSelfPasswordOtp() {
  const response = await fetch('/api/auth/self-password/send-otp', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; maskedEmail: string }>(response);
}

export async function updateSelfPassword(payload: {
  current_password?: string;
  otp_code?: string;
  new_password: string;
  confirm_password: string;
}) {
  const response = await fetch('/api/auth/self-password/update', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function startTestMode(email: string) {
  const response = await fetch('/api/test-mode/start', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ email }),
  });
  return parseJson<{ success: true }>(response);
}

export async function stopTestMode() {
  const response = await fetch('/api/test-mode/stop', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function getAuthMe() {
  const response = await fetch('/api/auth/me', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ user: BootstrapPayload['user'] }>(response);
}

export async function getUsers() {
  const response = await fetch('/api/users', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<UsersOverviewPayload>(response);
}

export async function createUserAccount(payload: Record<string, unknown>) {
  const response = await fetch('/api/users/create', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function updateUserAccount(email: string, payload: Record<string, unknown>) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}`, {
    method: 'PUT',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function lockUserAccount(email: string) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}/lock`, {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function unlockUserAccount(email: string) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}/unlock`, {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function deleteUserAccount(email: string) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}`, {
    method: 'DELETE',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function uploadBulkCounselors(formData: FormData) {
  const response = await fetch('/api/users/bulk-counselors-upload', {
    method: 'POST',
    credentials: 'include',
    body: formData,
  });
  return parseJson<{ success: true; message: string }>(response);
}

export async function getCounselorStudentList(email: string) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}/students`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ students: CounselorStudentRecord[] }>(response);
}

export async function uploadCounselorStudentList(email: string, formData: FormData) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}/students/upload`, {
    method: 'POST',
    credentials: 'include',
    body: formData,
  });
  return parseJson<{ success: true; count: number }>(response);
}

export async function saveCounselorStudentRow(email: string, payload: Record<string, unknown>) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}/students/save`, {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function deleteCounselorStudentRow(email: string, regNo: string) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}/students/${encodeURIComponent(regNo)}`, {
    method: 'DELETE',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function deleteAllCounselorStudentRows(email: string) {
  const response = await fetch(`/api/users/${encodeURIComponent(email)}/students`, {
    method: 'DELETE',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function getDepartments() {
  const response = await fetch('/api/departments', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ departments: DepartmentRecord[] }>(response);
}

export async function createDepartment(code: string, name: string) {
  const response = await fetch('/api/departments', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ code, name }),
  });
  return parseJson<{ success: true; department: DepartmentRecord }>(response);
}

export async function updateDepartment(id: number, code: string, name: string) {
  const response = await fetch(`/api/departments/${id}`, {
    method: 'PUT',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ code, name }),
  });
  return parseJson<{ success: true; department: DepartmentRecord }>(response);
}

export async function toggleDepartment(id: number) {
  const response = await fetch(`/api/departments/${id}/toggle`, {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; department: DepartmentRecord }>(response);
}

export async function deleteDepartment(id: number) {
  const response = await fetch(`/api/departments/${id}`, {
    method: 'DELETE',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function getReportsOverview(department?: string, year?: number | null) {
  const params = new URLSearchParams();
  if (department) params.set('department', department);
  if (year) params.set('year', String(year));
  const query = params.toString();
  const response = await fetch(`/api/reports/overview${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<ReportsOverviewPayload>(response);
}

export async function getSubjectsOverview(department?: string, year?: number | null, semester?: string) {
  const params = new URLSearchParams();
  if (department) params.set('department', department);
  if (year) params.set('year', String(year));
  if (semester) params.set('semester', semester);
  const query = params.toString();
  const response = await fetch(`/api/subjects/overview${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<SubjectsOverviewPayload>(response);
}

export async function createSubject(payload: {
  subject_code: string;
  subject_name: string;
  faculty_name: string;
  google_sheet_link: string;
  department: string;
  year_level: number;
  semester: string;
  academic_start_year: number;
  academic_end_year: number;
  class_sections: string[];
  faculty_allocations: Array<{
    faculty_name: string;
    class_sections: string[];
  }>;
}) {
  const response = await fetch('/api/subjects', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function parseSubjectSheet(google_sheet_link: string, department = '') {
  const response = await fetch('/api/subjects/parse-sheet', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ google_sheet_link, department }),
  });
  return parseJson<{
    success: true;
    subject_code: string;
    subject_name: string;
    faculty_name: string;
    faculty_names: string[];
    class_sections: string[];
    faculty_allocations: Array<{
      faculty_name: string;
      class_sections: string[];
    }>;
  }>(response);
}

export async function updateSubject(subjectId: number, payload: {
  subject_code: string;
  subject_name: string;
  faculty_name: string;
  google_sheet_link: string;
  semester: string;
  academic_start_year: number;
  academic_end_year: number;
  class_sections: string[];
  faculty_allocations: Array<{
    faculty_name: string;
    class_sections: string[];
  }>;
}) {
  const response = await fetch(`/api/subjects/${subjectId}`, {
    method: 'PUT',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function deleteSubject(subjectId: number) {
  const response = await fetch(`/api/subjects/${subjectId}`, {
    method: 'DELETE',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function getCdpOverview(filters?: {
  department?: string;
  year?: number | null;
  semester?: string;
  subject_id?: number | null;
}) {
  const params = new URLSearchParams();
  if (filters?.department) params.set('department', filters.department);
  if (filters?.year) params.set('year', String(filters.year));
  if (filters?.semester) params.set('semester', filters.semester);
  if (filters?.subject_id) params.set('subject_id', String(filters.subject_id));
  const query = params.toString();
  const response = await fetch(`/api/cdp/overview${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<CdpOverviewPayload>(response);
}

export async function rebuildCdpScope(filters: {
  department: string;
  year: number;
  semester: string;
  subject_id?: number | null;
  force?: boolean;
}) {
  const response = await fetch('/api/cdp/rebuild-scope', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(filters),
  });
  return parseJson<CdpOverviewPayload>(response);
}

export async function recheckCdpSubject(subjectId: number) {
  const response = await fetch(`/api/cdp/subjects/${subjectId}/recheck`, {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function syncCdpSubjectStudents(subjectId: number) {
  const response = await fetch(`/api/cdp/subjects/${subjectId}/sync-students`, {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; message: string }>(response);
}

export async function uploadMarksheet(formData: FormData) {
  const response = await fetch('/api/reports/upload', {
    method: 'POST',
    credentials: 'include',
    body: formData,
  });
  return parseJson<ReportUploadPayload>(response);
}

export async function getCounselorOverview() {
  const response = await fetch('/api/counselor/overview', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<CounselorOverviewPayload>(response);
}

export async function getCounselorTests() {
  const response = await fetch('/api/counselor/tests', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ tests: CounselorVisibleTestRecord[] }>(response);
}

export async function getCounselorMessages() {
  const response = await fetch('/api/counselor/messages', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ stats: CounselorMessageStats; messages: CounselorMessageRecord[] }>(response);
}

export async function getCounselorSendPage(testId: number, mode: 'app' | 'web' = 'app') {
  const response = await fetch(`/api/counselor/tests/${testId}/send?mode=${mode}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<CounselorSendPagePayload>(response);
}

export async function getCounselorNoticeSendPage(noticeId: number, mode: 'app' | 'web' = 'app') {
  const response = await fetch(`/api/counselor/notices/${noticeId}/send?mode=${mode}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<CounselorNoticeSendPagePayload>(response);
}

export async function sendSingleReport(formData: FormData) {
  const response = await fetch('/api/reports/send-single', {
    method: 'POST',
    credentials: 'include',
    body: formData,
  });
  return parseJson<SendSinglePreparedPayload>(response);
}

export async function sendSingleNotice(formData: FormData) {
  const response = await fetch('/api/notices/send-single', {
    method: 'POST',
    credentials: 'include',
    body: formData,
  });
  return parseJson<SendSinglePreparedPayload>(response);
}

export async function getTestDetail(testId: number) {
  const response = await fetch(`/api/tests/${testId}/detail`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<TestDetailPayload>(response);
}

export async function saveTestMeta(
  testId: number,
  payload: { test_name: string; semester: string; batch_name: string; section: string; overwrite_existing?: boolean },
) {
  const response = await fetch(`/api/tests/${testId}/meta`, {
    method: 'PUT',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true; overwrittenExisting?: boolean }>(response);
}

export async function saveTestMarks(
  testId: number,
  payload: { reg_no: string; marks: Record<string, string> },
) {
  const response = await fetch(`/api/tests/${testId}/marks/update`, {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

export async function toggleTestBlock(testId: number) {
  const response = await fetch(`/api/tests/${testId}/toggle-block`, {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; is_blocked: number }>(response);
}

export async function deleteTest(testId: number) {
  const response = await fetch(`/api/tests/${testId}`, {
    method: 'DELETE',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function getNoticesOverview(filters?: {
  department?: string;
  year?: number | null;
  status?: string;
  date_from?: string;
  date_to?: string;
  edit_id?: number | null;
}) {
  const params = new URLSearchParams();
  if (filters?.department) params.set('department', filters.department);
  if (filters?.year) params.set('year', String(filters.year));
  if (filters?.status) params.set('status', filters.status);
  if (filters?.date_from) params.set('date_from', filters.date_from);
  if (filters?.date_to) params.set('date_to', filters.date_to);
  if (filters?.edit_id) params.set('edit_id', String(filters.edit_id));
  const query = params.toString();
  const response = await fetch(`/api/notices/overview${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<NoticesOverviewPayload>(response);
}

export async function saveNotice(formData: FormData) {
  const response = await fetch(resolveDirectServerUrl('/api/notices/save'), {
    method: 'POST',
    credentials: 'include',
    body: formData,
  });
  return parseJson<{ success: true; noticeId: number }>(response);
}

export async function uploadNoticeAttachmentInChunks(noticeId: number, file: File, chunkSize = 256 * 1024) {
  const totalChunks = Math.max(1, Math.ceil(file.size / chunkSize));
  const uploadId = `${Date.now()}-${Math.random().toString(36).slice(2, 10)}`;

  for (let chunkIndex = 0; chunkIndex < totalChunks; chunkIndex += 1) {
    const chunk = file.slice(chunkIndex * chunkSize, Math.min(file.size, (chunkIndex + 1) * chunkSize));
    const formData = new FormData();
    formData.set('notice_id', String(noticeId));
    formData.set('upload_id', uploadId);
    formData.set('file_name', file.name || `attachment-${noticeId}`);
    formData.set('mime_type', file.type || '');
    formData.set('chunk_index', String(chunkIndex));
    formData.set('total_chunks', String(totalChunks));
    formData.set('chunk', chunk, file.name || `attachment-${noticeId}`);

    const response = await fetch(resolveDirectServerUrl('/api/notices/upload-chunk'), {
      method: 'POST',
      credentials: 'include',
      body: formData,
    });
    await parseJson<{ success: true; completed: boolean }>(response);
  }
}

export async function deleteNoticeRecord(noticeId: number) {
  const response = await fetch(`/api/notices/${noticeId}`, {
    method: 'DELETE',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function getActivityOverview(filters?: {
  department?: string;
  year?: number | null;
  semester?: string;
  test_name?: string;
  q?: string;
  sort?: string;
}) {
  const params = new URLSearchParams();
  if (filters?.department) params.set('department', filters.department);
  if (filters?.year) params.set('year', String(filters.year));
  if (filters?.semester) params.set('semester', filters.semester);
  if (filters?.test_name) params.set('test_name', filters.test_name);
  if (filters?.q) params.set('q', filters.q);
  if (filters?.sort) params.set('sort', filters.sort);
  const query = params.toString();
  const response = await fetch(`/api/activity/overview${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<ActivityOverviewPayload>(response);
}

export async function prefetchActivityScope(payload: {
  department: string;
  year: number;
}) {
  const response = await fetch('/api/activity/prefetch', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{
    success: true;
    department: string;
    year: number;
    prefetched: number;
    entries: ActivityOverviewPayload[];
  }>(response);
}

export async function getDashboardOverview() {
  const response = await fetch('/api/dashboard/overview', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<DashboardOverviewPayload>(response);
}

export async function getActivityScopeReport(filters?: {
  department?: string;
  year?: number | null;
  semester?: string;
  test_name?: string;
}) {
  const params = new URLSearchParams();
  if (filters?.department) params.set('department', filters.department);
  if (filters?.year) params.set('year', String(filters.year));
  if (filters?.semester) params.set('semester', filters.semester);
  if (filters?.test_name) params.set('test_name', filters.test_name);
  const query = params.toString();
  const response = await fetch(`/api/activity/scope-report${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<ActivityScopeReportPayload>(response);
}

export async function downloadActivityScopeReportPdf(filters?: {
  department?: string;
  year?: number | null;
  semester?: string;
  test_name?: string;
}) {
  const params = new URLSearchParams();
  if (filters?.department) params.set('department', filters.department);
  if (filters?.year) params.set('year', String(filters.year));
  if (filters?.semester) params.set('semester', filters.semester);
  if (filters?.test_name) params.set('test_name', filters.test_name);
  const query = params.toString();
  const response = await fetch(`/api/activity/scope-report/pdf${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/pdf,application/json' },
  });
  if (!response.ok) {
    const fallback = await response.json().catch(() => null);
    throw new Error(String(fallback?.error || 'Failed to download activity scope PDF.'));
  }
  const blob = await response.blob();
  const disposition = response.headers.get('content-disposition') || '';
  const fileNameMatch = disposition.match(/filename=\"?([^\";]+)\"?/i);
  return {
    blob,
    filename: fileNameMatch?.[1] || 'activity_scope_report.pdf',
  };
}

export async function getAdminMessagesOverview(filters?: {
  day?: string;
  q?: string;
  year?: string;
  month?: string;
  day_num?: string;
  limit?: number;
}) {
  const params = new URLSearchParams();
  if (filters?.day) params.set('day', filters.day);
  if (filters?.q) params.set('q', filters.q);
  if (filters?.year) params.set('year', filters.year);
  if (filters?.month) params.set('month', filters.month);
  if (filters?.day_num) params.set('day_num', filters.day_num);
  if (filters?.limit) params.set('limit', String(filters.limit));
  const query = params.toString();
  const response = await fetch(`/api/messages/overview${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<AdminMessagesOverviewPayload>(response);
}

export async function deleteAdminMessage(id: number) {
  const response = await fetch('/api/messages/delete', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ id }),
  });
  return parseJson<{ success: boolean; deleted: number }>(response);
}

export async function deleteAdminMessages(ids: number[]) {
  const response = await fetch('/api/messages/delete-bulk', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ ids }),
  });
  return parseJson<{ success: boolean; deleted: number }>(response);
}

export async function getMonitoringOverview(options?: { historyLimit?: number }) {
  const params = new URLSearchParams();
  if (options?.historyLimit) params.set('historyLimit', String(options.historyLimit));
  const query = params.toString();
  const response = await fetch(`/api/monitoring/overview${query ? `?${query}` : ''}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<MonitoringOverviewPayload>(response);
}

export async function getServerConsole(limit = 30) {
  const response = await fetch(`/api/admin/server-console?limit=${encodeURIComponent(String(limit))}`, {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<ServerConsolePayload>(response);
}

export async function logoutAllSessions() {
  const response = await fetch('/api/monitoring/logout-all', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function forceLogoutSession(email: string) {
  const response = await fetch(`/api/monitoring/force-logout/${encodeURIComponent(email)}`, {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function cleanupSessions() {
  const response = await fetch('/api/monitoring/cleanup', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true }>(response);
}

export async function sendSessionHeartbeat() {
  const response = await fetch('/api/session/heartbeat', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; now: string }>(response);
}

export async function getDatabaseOverview() {
  const response = await fetch('/api/database/overview', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<DatabaseOverviewPayload>(response);
}

export async function createDatabaseBackup(batch_name: string, overwrite = false) {
  const response = await fetch('/api/database/backup', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ batch_name, overwrite }),
  });
  return parseJson<{ success: true; message: string }>(response);
}

export async function deleteDatabaseBackup(backup_name: string, password: string) {
  const response = await fetch('/api/database/delete-backup', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ backup_name, password }),
  });
  return parseJson<{ success: true }>(response);
}

export async function restoreDatabaseBackup(backup_name: string, password: string) {
  const response = await fetch('/api/database/restore', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ backup_name, password }),
  });
  return parseJson<{ success: true; relogin?: boolean; reload?: boolean }>(response);
}

export async function clearExamDatabase(password: string) {
  const response = await fetch('/api/database/clear', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ password }),
  });
  return parseJson<{ success: true; relogin?: boolean }>(response);
}

export async function archiveAcademicYear(archive_label: string, password: string, overwrite = false) {
  const response = await fetch('/api/database/archive-year', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ archive_label, password, overwrite }),
  });
  return parseJson<{ success: true; reload?: boolean }>(response);
}

export async function enterArchiveView(archive_name: string) {
  const response = await fetch('/api/database/archive-view', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ archive_name }),
  });
  return parseJson<{ success: true; reload?: boolean }>(response);
}

export async function exitArchiveView() {
  const response = await fetch('/api/database/archive-view/exit', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; reload?: boolean }>(response);
}

export async function restoreArchiveYear(archive_name: string, password: string) {
  const response = await fetch('/api/database/restore-archive', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ archive_name, password }),
  });
  return parseJson<{ success: true; reload?: boolean; relogin?: boolean }>(response);
}

export async function deleteArchiveYear(archive_name: string, password: string) {
  const response = await fetch('/api/database/delete-archive', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ archive_name, password }),
  });
  return parseJson<{ success: true }>(response);
}

export async function getConfigOverview() {
  const response = await fetch('/api/config/overview', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<ConfigOverviewPayload>(response);
}

export async function downloadConfigExport() {
  const response = await fetch('/api/config/export', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  if (!response.ok) {
    throw new Error(await response.text().catch(() => 'Failed to download config.'));
  }
  return {
    blob: await response.blob(),
    fileName: response.headers.get('content-disposition')?.match(/filename="([^"]+)"/)?.[1] || 'shine-config.json',
  };
}

export async function importConfigPayload(payload: Record<string, unknown>) {
  const response = await fetch('/api/config/import', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<ConfigOverviewPayload>(response);
}

export async function updateConfig(payload: Record<string, unknown>) {
  const response = await fetch('/api/config/update', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true; appConfig: ConfigOverviewPayload['appConfig']; smtpStatus: ConfigOverviewPayload['smtpStatus']; relogin?: boolean }>(response);
}

export async function getNotificationState() {
  const response = await fetch('/api/notifications/state', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; readKeys: string[]; deletedKeys: string[] }>(response);
}

export async function markNotificationKeysRead(keys: string[]) {
  const response = await fetch('/api/notifications/read', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ keys }),
  });
  return parseJson<{ success: true; readKeys: string[]; deletedKeys: string[] }>(response);
}

export async function deleteNotificationKeys(keys: string[]) {
  const response = await fetch('/api/notifications/delete', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ keys }),
  });
  return parseJson<{ success: true; readKeys: string[]; deletedKeys: string[] }>(response);
}

export async function saveUserPreferences(payload: {
  theme?: 'light' | 'dark';
  desktopSettings?: Record<string, unknown>;
}) {
  const response = await fetch('/api/user/preferences', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{
    success: true;
    theme?: 'light' | 'dark' | '';
    desktopSettings?: Record<string, unknown>;
  }>(response);
}

export async function updateEnvContent(env_content: string) {
  const response = await fetch('/api/config/env-update', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify({ env_content }),
  });
  return parseJson<{ success: true }>(response);
}

export async function getSmtpStatus() {
  const response = await fetch('/api/config/smtp-status', {
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: true; status: ConfigOverviewPayload['smtpStatus'] }>(response);
}

export async function runSmtpTest() {
  const response = await fetch('/api/config/smtp-test', {
    method: 'POST',
    credentials: 'include',
    headers: { Accept: 'application/json' },
  });
  return parseJson<{ success: boolean; message: string }>(response);
}

export async function resetUserPassword(payload: {
  target_email: string;
  new_password: string;
  confirm_password: string;
  force_logout: boolean;
}) {
  const response = await fetch('/api/users/reset-password', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
      Accept: 'application/json',
    },
    body: JSON.stringify(payload),
  });
  return parseJson<{ success: true }>(response);
}

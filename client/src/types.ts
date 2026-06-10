export type Role = 'admin' | 'principal' | 'hod' | 'deo' | 'counselor';

export interface AppConfig {
  session_timeout: string;
  session_heartbeat_interval?: string;
  allow_concurrent_sessions: string;
  max_concurrent_sessions: string;
  enable_periodic_backups?: string;
  periodic_backup_hour?: string;
  periodic_backup_minute?: string;
  tutorial_master_enabled?: string;
  tutorial_counselor_enabled?: string;
  tutorial_hod_enabled?: string;
  tutorial_deo_enabled?: string;
  tutorial_principal_enabled?: string;
  disable_default_admin_on_new_system_admin?: string;
  require_otp_on_login: string;
  require_otp_on_password_reset: string;
  counselor_login_otp_enabled?: string;
  notice_copy_as_image?: string;
  activity_copy_as_image?: string;
  backup_storage_mode?: string;
  google_oauth_enabled: string;
  google_oauth_client_id: string;
  google_oauth_client_secret: string;
  google_oauth_allowed_domain?: string;
  google_oauth_redirect_base_url?: string;
  google_oauth_bulk_password_mode?: string;
  google_oauth_bulk_override_password?: string;
  google_drive_refresh_token?: string;
  google_drive_folder_id?: string;
  enable_counselor_batch_send: string;
  counselor_batch_send_delay_seconds: string;
  current_batch_year?: string;
  smtp_server?: string;
  smtp_port?: string;
  smtp_username?: string;
  smtp_password?: string;
  email_from?: string;
  color_primary: string;
  color_primary_dark: string;
  color_secondary: string;
  color_accent: string;
  color_success: string;
  color_warning: string;
  color_danger: string;
  color_info: string;
  color_bg_primary: string;
  color_bg_secondary: string;
  color_bg_card: string;
  color_text: string;
  color_text_dim: string;
  color_text_muted: string;
  color_border: string;
}

export interface ScopeRow {
  department: string;
  year_level: number;
}

export interface UserRecord {
  email: string;
  name: string;
  role: Role;
  department: string | null;
  year_level: number;
  is_active: number;
  is_locked: number;
  created_at?: string | null;
  max_students?: number;
  scopes?: ScopeRow[];
  student_count?: number;
  can_edit?: boolean;
  can_manage?: boolean;
}

export interface CounselorStudentRecord {
  reg_no: string;
  student_name: string;
  department: string;
  parent_phone: string;
  parent_email: string;
}

export interface UsersOverviewPayload {
  users: UserRecord[];
  departments: DepartmentRecord[];
  actorScopes: ScopeRow[];
  assignableRoles: Role[];
}

export interface DepartmentRecord {
  id: number;
  code: string;
  name: string;
  color: string;
  is_active: number;
}

export interface ReportTestRecord {
  id: number;
  test_id: number;
  test_name: string;
  batch_name: string;
  semester: string;
  department: string;
  year_level: number;
  section: string;
  uploaded_at: string;
  uploaded_by: string;
  uploaded_by_name: string;
  student_count: number;
  is_blocked: number;
}

export interface ReportsOverviewPayload {
  departments: DepartmentRecord[];
  selectedDepartment: string;
  availableYears: number[];
  selectedYear: number | null;
  tests: ReportTestRecord[];
}

export interface ReportUploadPayload {
  success: true;
  message: string;
  testId: number;
  studentCount: number;
  parserWarnings: string[];
}

export interface CounselorVisibleTestRecord extends ReportTestRecord {
  generated_count: number;
}

export interface CounselorMessageStats {
  total: number;
  today: number;
  week: number;
  month: number;
  unique: number;
}

export interface CounselorMessageRecord {
  id: number;
  reg_no: string;
  student_name: string;
  counselor_email: string;
  counselor_name: string;
  message_type: string;
  status: string;
  whatsapp_link: string;
  sent_at: string;
  test_id: number | null;
  send_mode: string;
}

export interface AdminMessageRecord extends CounselorMessageRecord {}

export interface MessageDayRecord {
  day: string;
  total: number;
  counselors: number;
}

export interface MessageCounselorSuggestion {
  name: string;
  email: string;
}

export interface AdminMessageStats {
  total: number;
  today: number;
  active_counselors: number;
}

export interface CounselorDashboardStudentInsight {
  reg_no: string;
  name: string;
  gpa: number;
  average_marks: number;
  failed_subjects?: number | null;
  subject_marks: Array<{
    subject: string;
    marks: number;
  }>;
}

export interface CounselorOverviewPayload {
  studentCount: number;
  testCount: number;
  messageStats: CounselorMessageStats;
  recentTests: CounselorVisibleTestRecord[];
  topPerformingStudents: CounselorDashboardStudentInsight[];
  studentsNeedImprovement: CounselorDashboardStudentInsight[];
  pendingNotices: NoticeRecord[];
}

export interface CounselorActivityRow {
  email: string;
  name: string;
  department: string;
  year_level: number;
  last_login: string;
  student_count: number;
  students_with_phone: number;
  total_messages: number;
  unique_students_messaged: number;
  pending_count: number;
  completion_pct: number;
  work_status: 'Complete' | 'Pending';
  tests_uploaded: number;
  week_messages: number;
}

export interface CounselorActivityResult {
  test_id: number | null;
  department: string;
  year_level: number;
  semester: string;
  test_name: string;
  rows: CounselorActivityRow[];
  stats: {
    total_counselors: number;
    complete: number;
    pending: number;
    avg_completion: number;
  };
}

export interface ActivityOverviewPayload {
  departments: DepartmentRecord[];
  selectedDepartment: string;
  availableYears: number[];
  selectedYear: number | null;
  selectedSemester: string;
  selectedTestName: string;
  searchQuery: string;
  sortMode: string;
  showDepartmentPicker: boolean;
  showYearPicker: boolean;
  showSemesterPicker: boolean;
  testStatus: Record<string, Record<string, boolean>>;
  result: CounselorActivityResult | null;
}

export interface ActivityScopeReportSection {
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
  rows: CounselorActivityRow[];
}

export interface ActivityScopeReportPayload {
  sections: ActivityScopeReportSection[];
}

export interface DashboardOverviewPayload {
  metrics: {
    departmentsCovered: number;
    totalTests: number;
    overallCompletion: number;
    totalMessages: number;
  };
  completion_overview: {
    overall: number;
    pending_counselors: number;
    department_labels: string[];
    department_values: number[];
    department_year_breakdown: Record<string, Record<number, number>>;
  };
  notice_completion_overview: {
    overall: number;
    pending_counselors: number;
    department_labels: string[];
    department_values: number[];
    department_year_breakdown: Record<string, Record<number, number>>;
  };
  counselor_activity: {
    labels: string[];
    values: number[];
  };
  leaderboard: Array<{
    email: string;
    name: string;
    department: string;
    year_level: number;
    student_count: number;
    unique_students_messaged: number;
    total_messages: number;
    completion_pct: number;
  }>;
  recentTests: ReportTestRecord[];
}

export interface NoticeScopePair {
  department: string;
  year_level: number;
}

export interface NoticeAttachmentRecord {
  id: number;
  notice_id: number;
  original_name: string;
  relative_path: string;
  mime_type: string;
  file_size: number;
  public_token: string;
}

export interface NoticeRecord {
  id: number;
  title: string;
  message_text: string;
  title_display: string;
  message_preview: string;
  send_to_all: number;
  created_by: string;
  created_role: string;
  created_at: string;
  created_day: string;
  created_by_name: string;
  attachment_count: number;
  attachments: NoticeAttachmentRecord[];
  scope_pairs: NoticeScopePair[];
  scope_labels: string[];
  completion_status: 'pending' | 'completed';
  completed_counselors: number;
  total_counselors: number;
  sent_students: number;
  total_students: number;
  can_manage_fully: boolean;
  student_count?: number;
}

export interface NoticeCompletionRow {
  email: string;
  name: string;
  department: string;
  year_level: number;
  student_count: number;
  message_count: number;
  total_notice_count: number;
  completed_notice_count: number;
  pending_notice_count: number;
  pending_notice_titles: string[];
  completion_state: 'pending' | 'completed' | 'no_students' | 'no_notices';
  completion_pct: number;
}

export interface NoticesOverviewPayload {
  departments: DepartmentRecord[];
  availableYears: number[];
  records: NoticeRecord[];
  completionRows: NoticeCompletionRow[];
  editNotice: NoticeRecord | null;
  filters: {
    department: string;
    year: number | null;
    status: string;
    date_from: string;
    date_to: string;
  };
}

export interface AdminMessagesOverviewPayload {
  filters: {
    day: string;
    q: string;
    year: string;
    month: string;
    day_num: string;
  };
  stats: AdminMessageStats;
  messages: AdminMessageRecord[];
  loadedCount: number;
  hasMore: boolean;
  groups: Array<{
    day: string;
    total: number;
    messages: AdminMessageRecord[];
  }>;
  messageDays: MessageDayRecord[];
  suggestions: MessageCounselorSuggestion[];
}

export interface CounselorSendReportRow {
  reg_no: string;
  student_name: string;
  parent_phone: string;
  department: string;
  marks: Record<string, string>;
  status: 'Generated' | 'Pending';
}

export interface CounselorSendPagePayload {
  testId: number;
  meta: TestDetailMeta;
  rows: CounselorSendReportRow[];
  defaultBatchName: string;
  sendMode: 'app' | 'web';
  batchSendEnabled: boolean;
  batchSendDelaySeconds: number;
}

export interface CounselorSendNoticeRow {
  reg_no: string;
  student_name: string;
  parent_phone: string;
  department: string;
  status: 'Generated' | 'Pending';
}

export interface CounselorNoticeSendPagePayload {
  noticeId: number;
  notice: {
    title: string;
    message_text: string;
    title_display: string;
  };
  rows: CounselorSendNoticeRow[];
  attachments: NoticeAttachmentRecord[];
  defaultTemplate: string;
  attachmentLinksText: string;
  sendMode: 'app' | 'web';
  batchSendEnabled: boolean;
  batchSendDelaySeconds: number;
}

export interface SendSinglePreparedPayload {
  success: true;
  status: 'prepared' | 'generated';
  reg_no?: string;
  wa_link?: string;
  delivery_token?: string;
}

export interface ReportStudentRow {
  reg_no: string;
  student_name: string;
  department: string;
  marks: Record<string, string>;
}

export interface TestDetailMeta {
  test_name: string;
  semester: string;
  department: string;
  year_level: number;
  section: string;
  batch_name: string;
  is_blocked?: number;
}

export interface TestDetailPayload {
  testId: number;
  meta: TestDetailMeta;
  subjects: string[];
  students: ReportStudentRow[];
  isReadOnly: boolean;
  isMetaReadOnly?: boolean;
  isMarksReadOnly?: boolean;
}

export interface SessionMonitoringRecord {
  session_id: string;
  user_email: string;
  name: string;
  role: string;
  department: string;
  ip_address: string;
  user_agent: string;
  login_time: string;
  last_activity: string;
  is_active: number;
  forced_logout: number;
  logout_reason: string;
  time_ago: string;
  status: 'Active' | 'Idle' | 'Inactive' | 'Unknown';
}

export interface SessionHistoryRecord {
  session_id: string;
  user_email: string;
  name: string;
  role: string;
  department: string;
  ip_address: string;
  login_time: string;
  last_activity: string;
  is_active: number;
  forced_logout: number;
  logout_reason: string;
  duration: string;
}

export interface SessionStatisticsRecord {
  active_sessions: number;
  today_sessions: number;
  avg_duration_minutes: number;
  logout_reasons: Record<string, number>;
  peak_concurrent: number;
  forced_logouts: number;
  mobile_sessions: number;
  desktop_sessions: number;
}

export interface MonitoringOverviewPayload {
  sessions: SessionMonitoringRecord[];
  stats: SessionStatisticsRecord;
  history: SessionHistoryRecord[];
  sessionLog: {
    ok: boolean;
    message: string;
  };
}

export interface DatabaseBackupRecord {
  name: string;
  size_kb: number;
  modified: string;
}

export interface DatabaseOverviewPayload {
  autoBackupFiles: DatabaseBackupRecord[];
  backupFiles: DatabaseBackupRecord[];
  archiveFiles: DatabaseBackupRecord[];
  currentBatchYear: string;
  backupStorageMode: 'local' | 'gdrive';
}

export interface SmtpStatusPayload {
  state: 'ready' | 'missing';
  label: string;
  detail: string;
  config: {
    server: string;
    username: string;
    email_from: string;
    port: string;
  };
}

export interface ConfigOverviewPayload {
  appConfig: AppConfig;
  envContent: string;
  smtpStatus: SmtpStatusPayload;
  resetUsers: UserRecord[];
}

export interface ServerConsolePayload {
  lines: string[];
  meta: string;
}

export interface SessionConflict {
  browser: string;
  device_type: string;
  ip_address: string;
  login_time: string;
}

export interface AuthUser {
  email: string;
  name: string;
  role: Role;
  department: string | null;
  year_level: number;
  scopes: ScopeRow[];
}

export interface BootstrapMetrics {
  totalUsers: number;
  counselorCount: number;
  activeSessions: number;
  messagesSent: number;
  departmentsCount: number;
  studentCount: number;
}

export interface AuthUiConfig {
  smtpReady: boolean;
  googleOauthEnabled: boolean;
  standardOtpLoginEnabled: boolean;
  forgotPasswordEnabled: boolean;
  selfPasswordOtpEnabled: boolean;
  adminCurrentPasswordFallbackEnabled: boolean;
}

export interface BootstrapPayload {
  appName: string;
  appVersion: string;
  appConfig: AppConfig;
  authUi: AuthUiConfig;
  nowLabel: string;
  user: AuthUser | null;
  testMode?: {
    active: boolean;
    sessionUser: AuthUser | null;
    targetUser: AuthUser | null;
  };
  navTabs: string[];
  defaultTab: string;
  metrics: BootstrapMetrics;
  counselorOverview?: CounselorOverviewPayload | null;
  counselorTests?: CounselorVisibleTestRecord[];
}

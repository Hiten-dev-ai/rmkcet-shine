import Database from 'better-sqlite3';
import { AsyncLocalStorage } from 'node:async_hooks';
import { randomBytes, randomUUID, scryptSync, timingSafeEqual, createHash } from 'node:crypto';
import { mkdirSync } from 'node:fs';
import { dirname } from 'node:path';
import { SHINE_DB_PATH } from './config.js';
import type { AuthUser, Role, ScopeRow } from './roles.js';
import { normalizeRole } from './roles.js';

mkdirSync(dirname(SHINE_DB_PATH), { recursive: true });

function ensureColumn(database: Database.Database, tableName: string, columnName: string, definition: string) {
  try {
    const columns = database.pragma(`table_info(${tableName})`) as Array<{ name?: string }>;
    if (columns.some((column) => String(column.name || '').trim().toLowerCase() === columnName.trim().toLowerCase())) {
      return;
    }
    database.exec(`ALTER TABLE ${tableName} ADD COLUMN ${columnName} ${definition}`);
  } catch {
    // Older or empty databases may not have every table during bootstrap.
  }
}

function configureDatabaseConnection(database: Database.Database) {
  database.pragma('foreign_keys = ON');
  database.pragma('journal_mode = WAL');
  ensureColumn(database, 'active_sessions', 'auth_method', "TEXT NOT NULL DEFAULT 'password'");
  ensureColumn(database, 'users', 'locked_until', 'TEXT');
  ensureColumn(database, 'users', 'login_email', 'TEXT');
  ensureColumn(database, 'users', 'designation', "TEXT NOT NULL DEFAULT ''");
  ensureColumn(database, 'student_marks', 'section', "TEXT NOT NULL DEFAULT ''");
  ensureColumn(database, 'cdp_subject_snapshots', 'mark_entry_statuses', "TEXT NOT NULL DEFAULT '{}'");
  try {
    database.exec(`
      UPDATE users
      SET login_email = LOWER(TRIM(email))
      WHERE COALESCE(TRIM(login_email), '') = '';
    `);
  } catch {
    // Older or empty databases may not have the users table during bootstrap.
  }
  try {
    database.exec(`
      CREATE TABLE IF NOT EXISTS subjects (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        subject_code TEXT NOT NULL,
        subject_name TEXT NOT NULL,
        faculty_name TEXT NOT NULL,
        google_sheet_link TEXT NOT NULL DEFAULT '',
        department TEXT NOT NULL,
        year_level INTEGER NOT NULL,
        semester TEXT NOT NULL DEFAULT '1',
        academic_start_year INTEGER,
        academic_end_year INTEGER,
        class_sections TEXT NOT NULL DEFAULT '[]',
        faculty_allocations TEXT NOT NULL DEFAULT '[]',
        created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
      );

      CREATE INDEX IF NOT EXISTS idx_subjects_scope
      ON subjects(department, year_level);

      CREATE INDEX IF NOT EXISTS idx_subjects_code
      ON subjects(subject_code);

      CREATE TABLE IF NOT EXISTS cdp_subject_snapshots (
        subject_id INTEGER PRIMARY KEY,
        department TEXT NOT NULL,
        year_level INTEGER NOT NULL,
        semester TEXT NOT NULL DEFAULT '1',
        summary_status TEXT NOT NULL DEFAULT 'unparsed',
        faculty_count INTEGER NOT NULL DEFAULT 0,
        allocated_class_count INTEGER NOT NULL DEFAULT 0,
        pending_faculty_count INTEGER NOT NULL DEFAULT 0,
        pending_class_count INTEGER NOT NULL DEFAULT 0,
        pending_date_count INTEGER NOT NULL DEFAULT 0,
        parsed_at TEXT,
        parser_error TEXT NOT NULL DEFAULT '',
        class_statuses TEXT NOT NULL DEFAULT '[]',
        faculty_statuses TEXT NOT NULL DEFAULT '[]',
        mark_entry_statuses TEXT NOT NULL DEFAULT '{}',
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        FOREIGN KEY(subject_id) REFERENCES subjects(id) ON DELETE CASCADE
      );

      CREATE INDEX IF NOT EXISTS idx_cdp_subject_snapshots_scope
      ON cdp_subject_snapshots(department, year_level, semester);

      CREATE TABLE IF NOT EXISTS oauth_login_attempts (
        id INTEGER PRIMARY KEY AUTOINCREMENT,
        attempt_id TEXT NOT NULL UNIQUE,
        email TEXT,
        display_name TEXT,
        auth_method TEXT NOT NULL DEFAULT 'google',
        ip_address TEXT,
        user_agent TEXT,
        attempt_time TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        failure_code TEXT,
        failure_reason TEXT
      );

      CREATE INDEX IF NOT EXISTS idx_oauth_login_attempts_time
      ON oauth_login_attempts(attempt_time DESC);

      CREATE TABLE IF NOT EXISTS notification_states (
        user_email TEXT NOT NULL,
        notification_key TEXT NOT NULL,
        status TEXT NOT NULL DEFAULT 'read',
        updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
        PRIMARY KEY(user_email, notification_key)
      );

      CREATE INDEX IF NOT EXISTS idx_notification_states_user_status
      ON notification_states(user_email, status);

      CREATE INDEX IF NOT EXISTS idx_sent_messages_sent_at
      ON sent_messages(sent_at DESC);

      CREATE INDEX IF NOT EXISTS idx_sent_messages_counselor_sent_at
      ON sent_messages(counselor_email, sent_at DESC);

      CREATE INDEX IF NOT EXISTS idx_counselor_students_counselor_active
      ON counselor_students(counselor_email, is_active);

      CREATE INDEX IF NOT EXISTS idx_student_marks_test_reg
      ON student_marks(test_id, reg_no);

      CREATE INDEX IF NOT EXISTS idx_sent_messages_counselor_test_reg
      ON sent_messages(counselor_email, test_id, reg_no);

      CREATE UNIQUE INDEX IF NOT EXISTS idx_users_login_role_unique
      ON users(login_email, role);

      CREATE INDEX IF NOT EXISTS idx_users_login_email
      ON users(login_email);
    `);
    ensureColumn(database, 'subjects', 'semester', "TEXT NOT NULL DEFAULT '1'");
    ensureColumn(database, 'subjects', 'academic_start_year', 'INTEGER');
    ensureColumn(database, 'subjects', 'academic_end_year', 'INTEGER');
    ensureColumn(database, 'subjects', 'class_sections', "TEXT NOT NULL DEFAULT '[]'");
    ensureColumn(database, 'subjects', 'faculty_allocations', "TEXT NOT NULL DEFAULT '[]'");
  } catch {
    // The table may not exist yet during first-run bootstrap.
  }
  return database;
}

function createDatabaseConnection() {
  return configureDatabaseConnection(new Database(SHINE_DB_PATH));
}

function createReadOnlyDatabaseConnection(dbPath: string) {
  const database = new Database(dbPath, { readonly: true, fileMustExist: true });
  database.pragma('foreign_keys = ON');
  database.pragma('query_only = ON');
  return database;
}

let liveDb = createDatabaseConnection();
const requestDbStorage = new AsyncLocalStorage<Database.Database>();

function getActiveDatabase() {
  return requestDbStorage.getStore() || liveDb;
}

export const db = new Proxy({} as Database.Database, {
  get(_target, prop, _receiver) {
    const database = getActiveDatabase();
    const value = Reflect.get(database as unknown as object, prop);
    return typeof value === 'function' ? value.bind(database) : value;
  },
  set(_target, prop, value) {
    const database = getActiveDatabase() as unknown as Record<PropertyKey, unknown>;
    database[prop] = value;
    return true;
  },
});

export function withDatabaseContext<T>(database: Database.Database, callback: () => T) {
  return requestDbStorage.run(database, callback);
}

export function openReadOnlyDatabase(dbPath: string) {
  return createReadOnlyDatabaseConnection(dbPath);
}

export function checkpointAndCloseDatabase() {
  if (!liveDb.open) return;
  try {
    liveDb.pragma('wal_checkpoint(TRUNCATE)');
  } catch {
    // Ignore checkpoint failures during shutdown/reload.
  }
  liveDb.close();
}

export function reconnectDatabase() {
  if (liveDb.open) {
    liveDb.close();
  }
  liveDb = createDatabaseConnection();
  return liveDb;
}

type SqlRow = Record<string, unknown>;

const APP_CONFIG_DEFAULTS: Record<string, string> = {
  session_timeout: '86400',
  allow_concurrent_sessions: 'false',
  max_concurrent_sessions: '1',
  session_monitoring_enabled: 'true',
  session_heartbeat_interval: '30',
  desktop_notification_poll_seconds: '30',
  notification_pending_threshold_days: '2',
  enable_periodic_backups: 'false',
  periodic_backup_hour: '0',
  periodic_backup_minute: '0',
  periodic_backup_last_run_date: '',
  require_otp_on_login: 'false',
  otp_login_lock_hours: '5',
  require_otp_on_password_reset: 'false',
  counselor_login_otp_enabled: 'true',
  notice_copy_as_image: 'false',
  activity_copy_as_image: 'false',
  notice_defaulter_copy_template: 'The Following Counsellors are yet to send the specified Notices\n\n{entries}',
  activity_defaulter_copy_template: 'The Following are all the counsellors who are yet to send results to their respective students\n\n{entries}',
  cdp_defaulter_copy_template: "The following subjects's CDP is not yet filled ,\n\n{entries}",
  backup_storage_mode: 'local',
  disable_default_admin_on_new_system_admin: 'false',
  google_oauth_enabled: 'false',
  google_oauth_client_id: '',
  google_oauth_client_secret: '',
  google_oauth_allowed_domain: '',
  google_oauth_redirect_base_url: '',
  google_oauth_bulk_password_mode: 'sheet',
  google_oauth_bulk_override_password: '',
  google_drive_refresh_token: '',
  google_drive_folder_id: '',
  tutorial_master_enabled: 'true',
  tutorial_counselor_enabled: 'true',
  tutorial_hod_enabled: 'true',
  tutorial_deo_enabled: 'true',
  tutorial_principal_enabled: 'true',
  smtp_server: '',
  smtp_port: '587',
  smtp_username: '',
  smtp_password: '',
  email_from: 'RMKCET Parent Connect <noreply@rmkcet.ac.in>',
  enable_counselor_batch_send: 'true',
  counselor_batch_send_delay_seconds: '4',
  desktop_send_workspace_enabled: 'true',
  desktop_send_target_preference: 'default_browser',
  color_primary: '#667eea',
  color_primary_dark: '#5a6fd6',
  color_secondary: '#764ba2',
  color_accent: '#a78bfa',
  color_success: '#25D366',
  color_warning: '#f59e0b',
  color_danger: '#ef4444',
  color_info: '#3b82f6',
  color_bg_primary: '#0a0c14',
  color_bg_secondary: '#0f1219',
  color_bg_card: 'rgba(20, 30, 50, 0.65)',
  color_text: '#e2e8f0',
  color_text_dim: '#94a3b8',
  color_text_muted: '#64748b',
  color_border: 'rgba(102, 126, 234, 0.18)',
};

let appConfigCache: Record<string, string> | null = null;

const ATTENDANCE_FIELD_KEYS = new Set(['attendance', 'att', 'attendence']);
const ALLOWED_TEST_NAMES = new Set(['IAT 1', 'IAT 2', 'MODEL EXAM']);

function normalizeMetricKey(key: string) {
  return String(key || '').toLowerCase().replace(/[^a-z0-9]/g, '');
}

function isAttendanceField(name: string) {
  return ATTENDANCE_FIELD_KEYS.has(normalizeMetricKey(name));
}

function normalizeTestName(rawName: string) {
  const text = String(rawName || '')
    .trim()
    .toUpperCase()
    .replace(/\s+/g, ' ');
  if (!text) return '';

  const compact = text.replace(/[^A-Z0-9]/g, '');
  if (text.includes('MODEL')) return 'MODEL EXAM';
  if (compact.endsWith('II') || compact.includes('IAT2') || compact.includes('UNITTEST2') || compact.includes('UNITTESTII')) {
    return 'IAT 2';
  }
  if (compact.endsWith('I') || compact.includes('IAT1') || compact.includes('UNITTEST1') || compact.includes('UNITTESTI')) {
    return 'IAT 1';
  }
  if (text.includes('IAT') || text.includes('UNIT TEST') || text.includes('INTERNAL ASSESSMENT')) {
    return 'IAT 1';
  }
  return '';
}

export function normalizeAllowedTestName(value: string) {
  const normalized = normalizeTestName(value);
  return ALLOWED_TEST_NAMES.has(normalized) ? normalized : '';
}

function normalizeLoginEmail(value: string) {
  return String(value || '').trim().toLowerCase();
}

function getUserLoginEmailValue(userRow: SqlRow | null | undefined) {
  return normalizeLoginEmail(String(userRow?.login_email || userRow?.email || ''));
}

function buildSyntheticAccountEmail(loginEmail: string, role: Role) {
  const safeLoginEmail = normalizeLoginEmail(loginEmail);
  const safeRole = normalizeRole(role);
  let candidate = `${safeLoginEmail}::__shine_role__:${safeRole}`;
  let counter = 2;
  while (getUserByEmail(candidate)) {
    candidate = `${safeLoginEmail}::__shine_role__:${safeRole}:${counter}`;
    counter += 1;
  }
  return candidate;
}

function rows<T extends SqlRow>(query: string, params: unknown[] = []) {
  return db.prepare(query).all(...params) as T[];
}

function row<T extends SqlRow>(query: string, params: unknown[] = []) {
  return (db.prepare(query).get(...params) as T | undefined) || null;
}

export function getAppConfig() {
  const config = { ...(appConfigCache || APP_CONFIG_DEFAULTS) } as Record<string, string>;
  try {
    const configRows = rows<{ key: string; value: string }>('SELECT key, value FROM app_config');
    for (const item of configRows) {
      config[item.key] = item.value;
    }
  } catch (error) {
    if (!(error instanceof Error) || !/database connection is not open/i.test(error.message)) {
      throw error;
    }
  }
  if (!String(config.smtp_server || '').trim()) config.smtp_server = String(process.env.SMTP_SERVER || '').trim();
  if (!String(config.smtp_port || '').trim()) config.smtp_port = String(process.env.SMTP_PORT || '587').trim();
  if (!String(config.smtp_username || '').trim()) config.smtp_username = String(process.env.SMTP_USERNAME || '').trim();
  if (!String(config.smtp_password || '').trim()) config.smtp_password = String(process.env.SMTP_PASSWORD || '').trim();
  if (!String(config.email_from || '').trim()) config.email_from = String(process.env.EMAIL_FROM || '').trim();
  appConfigCache = { ...config };
  return config;
}

export function updateAppConfig(key: string, value: string) {
  const now = new Date().toISOString().slice(0, 19).replace('T', ' ');
  db.prepare(`
    INSERT INTO app_config (key, value, updated_at)
    VALUES (?, ?, ?)
    ON CONFLICT(key) DO UPDATE SET value = excluded.value, updated_at = excluded.updated_at
  `).run(String(key || '').trim(), String(value ?? ''), now);
  appConfigCache = {
    ...getAppConfig(),
    [String(key || '').trim()]: String(value ?? ''),
  };
}

export function updateAppConfigBulk(settings: Record<string, string>) {
  const now = new Date().toISOString().slice(0, 19).replace('T', ' ');
  const statement = db.prepare(`
    INSERT INTO app_config (key, value, updated_at)
    VALUES (?, ?, ?)
    ON CONFLICT(key) DO UPDATE SET value = excluded.value, updated_at = excluded.updated_at
  `);
  const transaction = db.transaction((payload: Record<string, string>) => {
    for (const [key, value] of Object.entries(payload || {})) {
      statement.run(String(key || '').trim(), String(value ?? ''), now);
    }
  });
  transaction(settings || {});
  appConfigCache = {
    ...getAppConfig(),
    ...Object.fromEntries(Object.entries(settings || {}).map(([key, value]) => [String(key || '').trim(), String(value ?? '')])),
  };
}

export function getBatchNameForYearLevel(yearLevel: number, config: Record<string, string> = getAppConfig()) {
  const safeYear = Math.max(1, Number(yearLevel || 1) || 1);
  const rawBase = String(config.current_batch_year || '').trim();
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

function isLegacySha256(value: string) {
  return /^[a-fA-F0-9]{64}$/.test(String(value || '').trim());
}

export function verifyPassword(password: string, storedHash: string) {
  const stored = String(storedHash || '').trim();
  if (!stored) return false;
  if (isLegacySha256(stored)) {
    const legacy = createHash('sha256').update(password).digest('hex');
    return timingSafeEqual(Buffer.from(legacy, 'utf-8'), Buffer.from(stored.toLowerCase(), 'utf-8'));
  }
  if (!stored.startsWith('scrypt:')) return false;

  const [methodPart, salt, digestHex] = stored.split('$');
  if (!methodPart || !salt || !digestHex) return false;

  const parts = methodPart.split(':');
  if (parts.length !== 4 || parts[0] !== 'scrypt') return false;
  const n = Number(parts[1]);
  const r = Number(parts[2]);
  const p = Number(parts[3]);
  if (!Number.isFinite(n) || !Number.isFinite(r) || !Number.isFinite(p)) return false;

  const expected = Buffer.from(digestHex, 'hex');
  const derived = scryptSync(password, salt, expected.length, {
    N: n,
    r,
    p,
    // Werkzeug's default scrypt cost fits safely once we raise Node's conservative memory ceiling.
    maxmem: 512 * n * r * Math.max(p, 1),
  });
  return expected.length === derived.length && timingSafeEqual(expected, derived);
}

export function hashPassword(password: string) {
  const salt = randomBytes(12).toString('base64url');
  const N = 32768;
  const r = 8;
  const p = 1;
  const length = 64;
  const derived = scryptSync(password, salt, length, {
    N,
    r,
    p,
    maxmem: 512 * N * r * Math.max(p, 1),
  });
  return `scrypt:${N}:${r}:${p}$${salt}$${derived.toString('hex')}`;
}

export function getUserByIdentifier(identifier: string) {
  const ident = String(identifier || '').trim();
  if (!ident) return null;
  return (
    row<SqlRow>('SELECT * FROM users WHERE login_email = ? ORDER BY created_at ASC, id ASC LIMIT 1', [normalizeLoginEmail(ident)]) ||
    row<SqlRow>('SELECT * FROM users WHERE email = ?', [ident]) ||
    row<SqlRow>('SELECT * FROM users WHERE LOWER(name) = LOWER(?)', [ident])
  );
}

export function getUserByEmail(email: string) {
  return row<SqlRow>('SELECT * FROM users WHERE email = ?', [email]);
}

export function getUsersByLoginEmail(loginEmail: string) {
  return rows<SqlRow>(
    'SELECT * FROM users WHERE login_email = ? ORDER BY created_at ASC, id ASC',
    [normalizeLoginEmail(loginEmail)],
  );
}

export function getLoginCandidatesByIdentifier(identifier: string) {
  const ident = String(identifier || '').trim();
  if (!ident) return [];
  const normalized = normalizeLoginEmail(ident);
  const byLoginEmail = getUsersByLoginEmail(normalized);
  if (byLoginEmail.length) return byLoginEmail;
  const byInternalEmail = row<SqlRow>('SELECT * FROM users WHERE email = ?', [ident]);
  if (byInternalEmail) return [byInternalEmail];
  return rows<SqlRow>('SELECT * FROM users WHERE LOWER(name) = LOWER(?) ORDER BY created_at ASC, id ASC', [ident]);
}

export function updateUserPassword(email: string, newPassword: string) {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  const passwordHash = hashPassword(String(newPassword || ''));
  db.prepare(`
    UPDATE users
    SET password_hash = ?
    WHERE login_email = (
      SELECT login_email
      FROM users
      WHERE email = ?
      LIMIT 1
    )
  `).run(passwordHash, normalizedEmail);
}

export function createUser(
  email: string,
  password: string,
  name: string,
  role: Role = 'counselor',
  department: string | null = null,
  maxStudents = 30,
  canUploadStudents = true,
  yearLevel = 1,
  designation = '',
) {
  const normalizedEmail = normalizeLoginEmail(email);
  const normalizedName = String(name || '').trim();
  const normalizedDepartment = String(department || '').trim().toUpperCase();
  const safeRole = normalizeRole(role);
  if (!normalizedEmail || !normalizedName) throw new Error('Name and email are required.');

  const existingRole = row<SqlRow>(
    'SELECT * FROM users WHERE login_email = ? AND LOWER(COALESCE(role, \'\')) = ? LIMIT 1',
    [normalizedEmail, safeRole],
  );
  if (existingRole) {
    throw new Error('An account with this email already exists for the selected role.');
  }

  const existingGroupSeed = row<SqlRow>(
    'SELECT * FROM users WHERE login_email = ? ORDER BY created_at ASC, id ASC LIMIT 1',
    [normalizedEmail],
  );
  if (!existingGroupSeed && !String(password || '').trim()) {
    throw new Error('Password is required for a new email account.');
  }

  const effectiveName = existingGroupSeed
    ? String(existingGroupSeed.name || normalizedName || normalizedEmail)
    : normalizedName;
  const accountEmail = existingGroupSeed ? buildSyntheticAccountEmail(normalizedEmail, safeRole) : normalizedEmail;
  const passwordHash = existingGroupSeed
    ? String(existingGroupSeed.password_hash || '')
    : hashPassword(String(password || ''));
  const effectiveDesignation = safeRole === 'principal' ? String(designation || '').trim() || 'Higher Official' : '';
  db.prepare(`
    INSERT INTO users (
      email, login_email, password_hash, name, role, designation, department, year_level, max_students, can_upload_students
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
  `).run(
    accountEmail,
    normalizedEmail,
    passwordHash,
    effectiveName,
    safeRole,
    effectiveDesignation,
    normalizedDepartment || null,
    Number(yearLevel || 1),
    Number(maxStudents || 30),
    canUploadStudents ? 1 : 0,
  );

  return getUserByEmail(accountEmail);
}

export function updateUser(email: string, updates: Record<string, unknown>) {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  const currentUser = getUserByEmail(normalizedEmail);
  if (!currentUser) return null;
  const currentLoginEmail = getUserLoginEmailValue(currentUser) || normalizedEmail;
  const entries = Object.entries(updates || {}).filter(([, value]) => value !== undefined);
  if (!entries.length) return currentUser;

  const nextLoginEmail = updates.email !== undefined
    ? normalizeLoginEmail(String(updates.email || ''))
    : currentLoginEmail;
  const sharedPasswordSource = nextLoginEmail && nextLoginEmail !== currentLoginEmail
    ? row<SqlRow>('SELECT * FROM users WHERE login_email = ? AND email <> ? ORDER BY created_at ASC, id ASC LIMIT 1', [nextLoginEmail, normalizedEmail])
    : null;
  const nextPasswordHash = updates.password !== undefined
    ? hashPassword(String(updates.password || ''))
    : (sharedPasswordSource ? String(sharedPasswordSource.password_hash || '') : '');

  const sets: string[] = [];
  const values: unknown[] = [];
  for (const [key, value] of entries) {
    if (key === 'password') {
      continue;
    }
    if (key === 'email') {
      sets.push('login_email = ?');
      values.push(nextLoginEmail);
      continue;
    }
    sets.push(`${key} = ?`);
    values.push(value);
  }

  if (nextPasswordHash) {
    sets.push('password_hash = ?');
    values.push(nextPasswordHash);
  }

  if (entries.some(([key]) => key === 'name')) {
    db.prepare('UPDATE users SET name = ? WHERE login_email = ?').run(String(updates.name || '').trim(), currentLoginEmail);
  }

  values.push(normalizedEmail);
  db.prepare(`UPDATE users SET ${sets.join(', ')} WHERE email = ?`).run(...values);

  if (nextPasswordHash) {
    db.prepare('UPDATE users SET password_hash = ? WHERE login_email = ?').run(nextPasswordHash, nextLoginEmail || currentLoginEmail);
  }
  if (nextLoginEmail && nextLoginEmail !== currentLoginEmail) {
    const targetNameSeed = row<SqlRow>('SELECT * FROM users WHERE login_email = ? ORDER BY created_at ASC, id ASC LIMIT 1', [nextLoginEmail]);
    if (targetNameSeed?.name) {
      db.prepare('UPDATE users SET name = ? WHERE login_email = ?').run(String(targetNameSeed.name || '').trim(), nextLoginEmail);
    }
  }
  return getUserByEmail(normalizedEmail);
}

export function renameUserEmail(oldEmail: string, newEmail: string) {
  const oldValue = String(oldEmail || '').trim().toLowerCase();
  const newValue = String(newEmail || '').trim().toLowerCase();
  if (!oldValue || !newValue || oldValue === newValue) return;

  const transaction = db.transaction(() => {
    const existing = row<SqlRow>('SELECT * FROM users WHERE email = ?', [oldValue]);
    if (!existing) return;
    db.prepare(`
      INSERT INTO users (
        email, password_hash, name, department, year_level, role, created_at, last_login, last_activity, session_id,
        is_active, is_locked, lock_reason, max_students, can_upload_students, disable_login_otp, locked_until, login_email, designation
      )
      SELECT
        ?, password_hash, name, department, year_level, role, created_at, last_login, last_activity, session_id,
        is_active, is_locked, lock_reason, max_students, can_upload_students, COALESCE(disable_login_otp, 0), locked_until, COALESCE(login_email, email), COALESCE(designation, '')
      FROM users
      WHERE email = ?
    `).run(newValue, oldValue);
    db.prepare('UPDATE chief_admin_scopes SET chief_admin_email = ? WHERE chief_admin_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE active_sessions SET user_email = ? WHERE user_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE counselor_students SET counselor_email = ? WHERE counselor_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE sent_messages SET counselor_email = ? WHERE counselor_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE counselor_mark_overrides SET counselor_email = ? WHERE counselor_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE counselor_time_scores SET counselor_email = ? WHERE counselor_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE password_reset_tokens SET user_email = ? WHERE user_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE notices SET created_by = ? WHERE created_by = ?').run(newValue, oldValue);
    db.prepare('UPDATE notice_deliveries SET counselor_email = ? WHERE counselor_email = ?').run(newValue, oldValue);
    db.prepare('UPDATE test_metadata SET uploaded_by = ? WHERE uploaded_by = ?').run(newValue, oldValue);
    db.prepare('UPDATE student_marks SET uploaded_by = ? WHERE uploaded_by = ?').run(newValue, oldValue);
    db.prepare('UPDATE oauth_login_attempts SET email = ? WHERE LOWER(COALESCE(email, \'\')) = ?').run(newValue, oldValue);
    db.prepare('DELETE FROM users WHERE email = ?').run(oldValue);
  });
  transaction();
}

export function setChiefAdminScopes(email: string, scopes: ScopeRow[]) {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  const cleaned = Array.from(
    new Set(
      (scopes || [])
        .map((scope) => `${String(scope.department || '').trim().toUpperCase()}::${Number(scope.year_level || 0)}`)
        .filter((value) => {
          const [department, yearValue] = value.split('::');
          const yearLevel = Number(yearValue || 0);
          return !!department && yearLevel >= 1 && yearLevel <= 4;
        }),
    ),
  ).map((value) => {
    const [department, yearValue] = value.split('::');
    return { department, year_level: Number(yearValue || 1) };
  });

  const transaction = db.transaction(() => {
    db.prepare('DELETE FROM chief_admin_scopes WHERE chief_admin_email = ?').run(normalizedEmail);
    const statement = db.prepare(`
      INSERT INTO chief_admin_scopes (chief_admin_email, department, year_level)
      VALUES (?, ?, ?)
    `);
    for (const scope of cleaned) {
      statement.run(normalizedEmail, scope.department, scope.year_level);
    }
  });
  transaction();
}

export function deleteUser(email: string) {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  const transaction = db.transaction(() => {
    db.prepare('DELETE FROM chief_admin_scopes WHERE chief_admin_email = ?').run(normalizedEmail);
    db.prepare('DELETE FROM counselor_mark_overrides WHERE counselor_email = ?').run(normalizedEmail);
    db.prepare('DELETE FROM counselor_time_scores WHERE counselor_email = ?').run(normalizedEmail);
    db.prepare('DELETE FROM counselor_students WHERE counselor_email = ?').run(normalizedEmail);
    db.prepare('DELETE FROM sent_messages WHERE counselor_email = ?').run(normalizedEmail);
    db.prepare('DELETE FROM notice_deliveries WHERE counselor_email = ?').run(normalizedEmail);
    db.prepare('DELETE FROM password_reset_tokens WHERE user_email = ?').run(normalizedEmail);
    db.prepare('DELETE FROM active_sessions WHERE user_email = ?').run(normalizedEmail);
    db.prepare('UPDATE notices SET created_by = NULL WHERE created_by = ?').run(normalizedEmail);
    db.prepare('DELETE FROM users WHERE email = ?').run(normalizedEmail);
  });
  transaction();
}

export function lockUser(email: string, reason = 'Locked by admin', lockedUntil: string | null = null) {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  const transaction = db.transaction(() => {
    db.prepare('UPDATE users SET is_locked = 1, is_active = 0, lock_reason = ?, locked_until = ? WHERE email = ?').run(reason, lockedUntil, normalizedEmail);
    db.prepare("UPDATE active_sessions SET is_active = 0, forced_logout = 1, logout_reason = 'account_locked' WHERE user_email = ? AND is_active = 1").run(normalizedEmail);
    db.prepare('UPDATE users SET session_id = NULL WHERE email = ?').run(normalizedEmail);
  });
  transaction();
}

export function unlockUser(email: string) {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  db.prepare('UPDATE users SET is_locked = 0, is_active = 1, lock_reason = NULL, locked_until = NULL WHERE email = ?').run(normalizedEmail);
}

export function lockUserForDuration(email: string, reason: string, durationMs: number) {
  const lockedUntil = new Date(Date.now() + Math.max(1, durationMs)).toISOString().slice(0, 19).replace('T', ' ');
  lockUser(email, reason, lockedUntil);
  return lockedUntil;
}

export function getScopesForUser(email: string): ScopeRow[] {
  return rows<{ department: string; year_level: number }>(
    'SELECT department, year_level FROM chief_admin_scopes WHERE chief_admin_email = ? ORDER BY department, year_level',
    [email],
  ).map((item) => ({
    department: String(item.department || '').toUpperCase(),
    year_level: Number(item.year_level || 1),
  }));
}

export function getAllowedScopesForUser(user: AuthUser | null) {
  if (!user) return null;
  if (user.role === 'admin' || user.role === 'principal') return null;
  if (user.role !== 'hod' && user.role !== 'deo') return null;
  return new Set(user.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
}

export function toAuthUser(userRow: SqlRow): AuthUser {
  const email = String(userRow.email || userRow.user_email || '').toLowerCase();
  const role = normalizeRole(userRow.role);
  return {
    email,
    login_email: getUserLoginEmailValue(userRow) || email,
    name: String(userRow.name || email),
    role,
    designation: role === 'principal' ? String(userRow.designation || '').trim() : '',
    department: userRow.department ? String(userRow.department) : null,
    year_level: Number(userRow.year_level || 1),
    scopes: getScopesForUser(email),
  };
}

function parseUserAgent(userAgent: string) {
  const value = String(userAgent || '');
  let deviceType = 'Desktop';
  if (/ipad|tablet/i.test(value)) deviceType = 'Tablet';
  else if (/android|iphone|mobile/i.test(value)) deviceType = 'Mobile';

  let browser = 'Unknown';
  if (/edg/i.test(value)) browser = 'Edge';
  else if (/chrome/i.test(value)) browser = 'Chrome';
  else if (/firefox/i.test(value)) browser = 'Firefox';
  else if (/safari/i.test(value)) browser = 'Safari';

  return { deviceType, browser };
}

function parseSqlDate(value: string) {
  const raw = String(value || '').trim();
  if (!raw) return null;
  const normalized = raw.includes('T') ? raw : raw.replace(' ', 'T');
  const assumedUtc = /(?:Z|[+-]\d{2}:\d{2})$/i.test(normalized) ? normalized : `${normalized}Z`;
  const timestamp = Date.parse(assumedUtc);
  if (!Number.isFinite(timestamp)) return null;
  return new Date(timestamp);
}

function formatTimeAgo(value: string) {
  const date = parseSqlDate(value);
  if (!date) return 'Unknown';
  const diffSeconds = Math.max(0, Math.floor((Date.now() - date.getTime()) / 1000));
  if (diffSeconds < 60) return `${diffSeconds}s ago`;
  if (diffSeconds < 3600) return `${Math.floor(diffSeconds / 60)}m ago`;
  if (diffSeconds < 86400) return `${Math.floor(diffSeconds / 3600)}h ago`;
  return `${Math.floor(diffSeconds / 86400)}d ago`;
}

export function getActiveSessionForUser(email: string) {
  const session = row<SqlRow>(
    'SELECT * FROM active_sessions WHERE user_email = ? AND is_active = 1 ORDER BY login_time DESC LIMIT 1',
    [email],
  );
  if (!session) return null;
  const parsed = parseUserAgent(String(session.user_agent || ''));
  return {
    browser: parsed.browser,
    device_type: parsed.deviceType,
    ip_address: String(session.ip_address || ''),
    login_time: String(session.login_time || ''),
  };
}

export function forceLogoutUser(email: string, reason = 'admin_action') {
  const normalizedEmail = String(email || '').trim().toLowerCase();
  db.prepare("UPDATE active_sessions SET is_active = 0, forced_logout = 1, logout_reason = ? WHERE user_email = ? AND is_active = 1").run(reason, normalizedEmail);
  db.prepare('UPDATE users SET session_id = NULL WHERE email = ?').run(normalizedEmail);
}

export function getActiveSessions() {
  return rows<SqlRow>(
    `
      SELECT s.*, u.name, u.role, u.department
      FROM active_sessions s
      LEFT JOIN users u ON s.user_email = u.email
      WHERE s.is_active = 1
      ORDER BY s.last_activity DESC
    `,
  ).map((item) => {
    const lastActivity = String(item.last_activity || '');
    const date = parseSqlDate(lastActivity);
    const diff = date ? Math.floor((Date.now() - date.getTime()) / 1000) : NaN;
    let status: SessionMonitoringRecord['status'] = 'Unknown';
    if (Number.isFinite(diff)) {
      if (diff < 120) status = 'Active';
      else if (diff < 600) status = 'Idle';
      else status = 'Inactive';
    }
    return {
      session_id: String(item.session_id || ''),
      user_email: String(item.user_email || ''),
      login_email: getUserLoginEmailValue(item) || String(item.user_email || ''),
      name: String(item.name || item.user_email || ''),
      role: String(item.role || ''),
      department: String(item.department || ''),
      auth_method: String(item.auth_method || 'password'),
      ip_address: String(item.ip_address || ''),
      user_agent: String(item.user_agent || ''),
      login_time: String(item.login_time || ''),
      last_activity: lastActivity,
      is_active: Number(item.is_active || 0),
      forced_logout: Number(item.forced_logout || 0),
      logout_reason: String(item.logout_reason || ''),
      time_ago: formatTimeAgo(lastActivity),
      status,
    } satisfies SessionMonitoringRecord;
  });
}

export function clearInactiveSessions() {
  db.prepare('DELETE FROM active_sessions WHERE is_active = 0').run();
}

export function logoutAllUsers() {
  db.prepare("UPDATE active_sessions SET is_active = 0, logout_reason = 'admin_logout_all'").run();
  db.prepare('UPDATE users SET session_id = NULL').run();
}

export function getSessionStatistics(): SessionStatisticsRecord {
  const activeSessions = Number(row<{ count: number }>('SELECT COUNT(*) AS count FROM active_sessions WHERE is_active = 1')?.count || 0);
  const todaySessions = Number(row<{ count: number }>("SELECT COUNT(*) AS count FROM active_sessions WHERE DATE(login_time) = DATE('now')")?.count || 0);
  const avgDuration = Number(
    row<{ avg_duration: number }>(
      `
        SELECT AVG((JULIANDAY(COALESCE(last_activity, login_time)) - JULIANDAY(login_time)) * 24 * 60) AS avg_duration
        FROM active_sessions
        WHERE is_active = 0 AND logout_reason IS NOT NULL
      `,
    )?.avg_duration || 0,
  );
  const peakConcurrent = Number(
    row<{ peak_count: number }>(
      `
        SELECT MAX(concurrent_count) AS peak_count
        FROM (
          SELECT COUNT(*) AS concurrent_count
          FROM active_sessions
          GROUP BY DATE(login_time), strftime('%H', login_time)
        )
      `,
    )?.peak_count || 0,
  );
  const forcedLogouts = Number(row<{ count: number }>('SELECT COUNT(*) AS count FROM active_sessions WHERE forced_logout = 1')?.count || 0);
  const mobileSessions = Number(
    row<{ count: number }>(
      `
        SELECT COUNT(*) AS count
        FROM active_sessions
        WHERE user_agent LIKE '%Mobile%' OR user_agent LIKE '%Android%' OR user_agent LIKE '%iPhone%'
      `,
    )?.count || 0,
  );
  const desktopSessions = Number(
    row<{ count: number }>(
      `
        SELECT COUNT(*) AS count
        FROM active_sessions
        WHERE user_agent NOT LIKE '%Mobile%' AND user_agent NOT LIKE '%Android%' AND user_agent NOT LIKE '%iPhone%'
      `,
    )?.count || 0,
  );

  const logoutReasonRows = rows<{ logout_reason: string; cnt: number }>(
    `
      SELECT logout_reason, COUNT(*) AS cnt
      FROM active_sessions
      WHERE is_active = 0 AND logout_reason IS NOT NULL
      GROUP BY logout_reason
    `,
  );

  const logoutReasons: Record<string, number> = {};
  for (const item of logoutReasonRows) {
    logoutReasons[String(item.logout_reason || '')] = Number(item.cnt || 0);
  }

  return {
    active_sessions: activeSessions,
    today_sessions: todaySessions,
    avg_duration_minutes: Math.round(avgDuration * 10) / 10,
    logout_reasons: logoutReasons,
    peak_concurrent: peakConcurrent,
    forced_logouts: forcedLogouts,
    mobile_sessions: mobileSessions,
    desktop_sessions: desktopSessions,
  };
}

export function recordAuthFailureAttempt(payload: {
  email?: string | null;
  display_name?: string | null;
  ip_address?: string | null;
  user_agent?: string | null;
  auth_method?: string | null;
  failure_code: string;
  failure_reason: string;
}) {
  const now = new Date().toISOString().slice(0, 19).replace('T', ' ');
  db.prepare(`
    INSERT INTO oauth_login_attempts (
      attempt_id, email, display_name, auth_method, ip_address, user_agent, attempt_time, failure_code, failure_reason
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
  `).run(
    randomUUID(),
    String(payload.email || '').trim().toLowerCase() || null,
    String(payload.display_name || '').trim() || null,
    String(payload.auth_method || 'google').trim().toLowerCase() || 'google',
    String(payload.ip_address || '').trim(),
    String(payload.user_agent || '').trim(),
    now,
    String(payload.failure_code || '').trim() || 'auth_failed',
    String(payload.failure_reason || '').trim() || 'Authentication failed.',
  );
}

export function recordOauthLoginAttempt(payload: {
  email?: string | null;
  display_name?: string | null;
  ip_address?: string | null;
  user_agent?: string | null;
  failure_code: string;
  failure_reason: string;
}) {
  recordAuthFailureAttempt({
    ...payload,
    auth_method: 'google',
  });
}

export function getSessionLastActivityInfo(sessionId: string) {
  const item = row<{ last_activity: string | null; is_active: number | null; user_email: string | null }>(
    'SELECT last_activity, is_active, user_email FROM active_sessions WHERE session_id = ? ORDER BY login_time DESC LIMIT 1',
    [String(sessionId || '').trim()],
  );
  return item
    ? {
        last_activity: String(item.last_activity || ''),
        is_active: Number(item.is_active || 0),
        user_email: String(item.user_email || '').trim().toLowerCase(),
      }
    : null;
}

export function getOauthAttemptStatistics() {
  const totalUnregisteredAttempts = Number(
    row<{ count: number }>(
      "SELECT COUNT(*) AS count FROM oauth_login_attempts WHERE LOWER(COALESCE(failure_code, '')) = 'user_not_linked'",
    )?.count || 0,
  );
  const todayUnregisteredAttempts = Number(
    row<{ count: number }>(
      "SELECT COUNT(*) AS count FROM oauth_login_attempts WHERE LOWER(COALESCE(failure_code, '')) = 'user_not_linked' AND DATE(attempt_time) = DATE('now')",
    )?.count || 0,
  );
  const latestUnregisteredAttempt = row<{
    email: string;
    display_name: string;
    attempt_time: string;
    failure_reason: string;
  }>(
    `
      SELECT email, display_name, attempt_time, failure_reason
      FROM oauth_login_attempts
      WHERE LOWER(COALESCE(failure_code, '')) = 'user_not_linked'
      ORDER BY attempt_time DESC
      LIMIT 1
    `,
  );
  return {
    total_unregistered_attempts: totalUnregisteredAttempts,
    today_unregistered_attempts: todayUnregisteredAttempts,
    latest_unregistered_attempt_email: String(latestUnregisteredAttempt?.email || ''),
    latest_unregistered_attempt_name: String(latestUnregisteredAttempt?.display_name || ''),
    latest_unregistered_attempt_time: String(latestUnregisteredAttempt?.attempt_time || ''),
    latest_unregistered_attempt_reason: String(latestUnregisteredAttempt?.failure_reason || ''),
  };
}

export function getSessionHistory(limit = 100, userEmail?: string | null) {
  const query = userEmail
    ? `
        SELECT s.*, u.name, u.role, u.department
        FROM active_sessions s
        LEFT JOIN users u ON s.user_email = u.email
        WHERE s.user_email = ?
        ORDER BY s.login_time DESC
        LIMIT ?
      `
    : `
        SELECT s.*, u.name, u.role, u.department
        FROM active_sessions s
        LEFT JOIN users u ON s.user_email = u.email
        ORDER BY s.login_time DESC
        LIMIT ?
      `;
  const params = userEmail ? [String(userEmail || '').trim().toLowerCase(), limit] : [limit];
  const sessionRows = rows<SqlRow>(query, params).map((item) => {
    const loginDate = parseSqlDate(String(item.login_time || ''));
    const lastDate = parseSqlDate(String(item.last_activity || item.login_time || ''));
    let duration = 'Unknown';
    if (loginDate && lastDate) {
      const minutes = Math.max(0, Math.floor((lastDate.getTime() - loginDate.getTime()) / 60000));
      duration = minutes < 60 ? `${minutes}m` : `${Math.floor(minutes / 60)}h ${minutes % 60}m`;
    }
    return {
      session_id: String(item.session_id || ''),
      user_email: String(item.user_email || ''),
      login_email: getUserLoginEmailValue(item) || String(item.user_email || ''),
      name: String(item.name || item.user_email || ''),
      role: String(item.role || ''),
      department: String(item.department || ''),
      auth_method: String(item.auth_method || 'password'),
      ip_address: String(item.ip_address || ''),
      login_time: String(item.login_time || ''),
      last_activity: String(item.last_activity || ''),
      is_active: Number(item.is_active || 0),
      forced_logout: Number(item.forced_logout || 0),
      logout_reason: String(item.logout_reason || ''),
      duration,
    } satisfies SessionHistoryRecord;
  });

  const oauthAttemptQuery = userEmail
    ? `
        SELECT *
        FROM oauth_login_attempts
        WHERE LOWER(COALESCE(email, '')) = ?
          AND LOWER(COALESCE(failure_code, '')) IN ('user_not_linked', 'password_unauthorized')
        ORDER BY attempt_time DESC
        LIMIT ?
      `
    : `
        SELECT *
        FROM oauth_login_attempts
        WHERE LOWER(COALESCE(failure_code, '')) IN ('user_not_linked', 'password_unauthorized')
        ORDER BY attempt_time DESC
        LIMIT ?
      `;
  const oauthAttemptParams = userEmail ? [String(userEmail || '').trim().toLowerCase(), limit] : [limit];
  const oauthAttemptRows = rows<SqlRow>(oauthAttemptQuery, oauthAttemptParams).map((item) => ({
    session_id: `oauth-attempt:${String(item.attempt_id || item.id || '')}`,
    user_email: String(item.email || ''),
    login_email: String(item.email || ''),
    name: String(item.display_name || item.email || 'Failed User'),
    role: 'Failed Attempt',
    department: '',
    auth_method:
      String(item.failure_code || '').trim().toLowerCase() === 'password_unauthorized'
        ? 'password_failed'
        : String(item.auth_method || '').trim().toLowerCase() === 'google'
        ? 'google_unregistered'
        : String(item.auth_method || 'password'),
    ip_address: String(item.ip_address || ''),
    login_time: String(item.attempt_time || ''),
    last_activity: String(item.attempt_time || ''),
    is_active: 0,
    forced_logout: 0,
    logout_reason: String(item.failure_reason || 'Authentication failed.'),
    duration: 'Failed Attempt',
  } satisfies SessionHistoryRecord));

  return [...sessionRows, ...oauthAttemptRows]
    .sort((a, b) => Date.parse(String(b.login_time || '').replace(' ', 'T')) - Date.parse(String(a.login_time || '').replace(' ', 'T')))
    .slice(0, limit);
}

export function checkUserAccess(email: string) {
  const user = getUserByEmail(email);
  if (!user) return { allowed: false, message: 'User not found' };
  const lockedUntilValue = String(user.locked_until || '').trim();
  const lockedUntilDate = parseSqlDate(lockedUntilValue);
  if (Number(user.is_locked) && lockedUntilDate && lockedUntilDate.getTime() <= Date.now()) {
    unlockUser(String(user.email || ''));
    const refreshedUser = getUserByEmail(String(user.email || ''));
    if (refreshedUser) {
      if (!Number(refreshedUser.is_active)) return { allowed: false, message: 'Account deactivated' };
      if (Number(refreshedUser.is_locked)) return { allowed: false, message: 'Account locked' };
    }
    return { allowed: true, message: 'Access granted' };
  }
  if (!Number(user.is_active) && !Number(user.is_locked)) return { allowed: false, message: 'Account deactivated' };
  if (Number(user.is_locked)) {
    const reason = String(user.lock_reason || '').trim().toLowerCase();
    if (reason === 'password_unauthorized' && lockedUntilDate) {
      const unlockAt = lockedUntilDate.toLocaleString('en-GB', {
        day: '2-digit',
        month: 'short',
        year: 'numeric',
        hour: '2-digit',
        minute: '2-digit',
        hour12: false,
      });
      return {
        allowed: false,
        message: `Account locked until ${unlockAt} due to repeated unauthorized OTP attempts. Please contact system admin for unblock.`,
      };
    }
    return { allowed: false, message: 'Account locked' };
  }
  return { allowed: true, message: 'Access granted' };
}

export function registerSession(userEmail: string, ipAddress: string, userAgent: string, forceLogoutOthers: boolean, authMethod = 'password') {
  const config = getAppConfig();
  const allowConcurrent = String(config.allow_concurrent_sessions || 'false').toLowerCase() === 'true';
  const sessionId = randomUUID();
  const now = new Date().toISOString().slice(0, 19).replace('T', ' ');

  if (forceLogoutOthers || !allowConcurrent) {
    db.prepare("UPDATE active_sessions SET is_active = 0, logout_reason = 'new_login' WHERE user_email = ? AND is_active = 1").run(userEmail);
  }

  db.prepare(`
    INSERT INTO active_sessions (
      session_id, user_email, login_time, last_activity, ip_address, user_agent, browser_info, tab_id, is_active, forced_logout, auth_method
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, 1, 0, ?)
  `).run(sessionId, userEmail, now, now, ipAddress, userAgent, userAgent.slice(0, 100), randomUUID(), authMethod);

  db.prepare('UPDATE users SET last_login = ?, last_activity = ?, session_id = ? WHERE email = ?').run(now, now, sessionId, userEmail);
  return sessionId;
}

export function logoutSession(sessionId: string, reason = 'logout') {
  db.prepare('UPDATE active_sessions SET is_active = 0, logout_reason = ? WHERE session_id = ?').run(reason, sessionId);
  db.prepare('UPDATE users SET session_id = NULL WHERE session_id = ?').run(sessionId);
}

export function getLogoutReasonForSession(sessionId: string) {
  const record = row<{ logout_reason: string | null }>(
    'SELECT logout_reason FROM active_sessions WHERE session_id = ? ORDER BY login_time DESC LIMIT 1',
    [String(sessionId || '').trim()],
  );
  return String(record?.logout_reason || '').trim() || null;
}

export function validateSession(sessionId: string) {
  if (!sessionId) return null;
  const session = row<SqlRow>(
    `SELECT s.*, u.name, u.role, u.department, u.year_level, u.is_active AS user_active, u.is_locked, u.login_email, u.designation
     FROM active_sessions s
     LEFT JOIN users u ON u.email = s.user_email
     WHERE s.session_id = ?`,
    [sessionId],
  );
  if (!session || !Number(session.is_active)) return null;
  if (!Number(session.user_active) || Number(session.is_locked)) return null;

  const config = getAppConfig();
  const timeoutSeconds = Number(config.session_timeout || 86400);
  const lastActivity = String(session.last_activity || '');
  if (lastActivity) {
    const parsedLastActivity = parseSqlDate(lastActivity);
    const diffSeconds = parsedLastActivity ? (Date.now() - parsedLastActivity.getTime()) / 1000 : NaN;
    if (Number.isFinite(diffSeconds) && diffSeconds > timeoutSeconds) {
      logoutSession(sessionId, 'session_timeout');
      return null;
    }
  }

  const now = new Date().toISOString().slice(0, 19).replace('T', ' ');
  db.prepare('UPDATE active_sessions SET last_activity = ? WHERE session_id = ?').run(now, sessionId);
  db.prepare('UPDATE users SET last_activity = ? WHERE email = ?').run(now, String(session.user_email || ''));
  return toAuthUser(session);
}

export function getDashboardMetrics(user: AuthUser | null) {
  const totalUsers = Number((row<{ count: number }>('SELECT COUNT(*) AS count FROM users')?.count || 0));
  const counselorCount = Number((row<{ count: number }>("SELECT COUNT(*) AS count FROM users WHERE LOWER(role) = 'counselor'")?.count || 0));
  const activeSessions = Number((row<{ count: number }>('SELECT COUNT(*) AS count FROM active_sessions WHERE is_active = 1')?.count || 0));
  const messagesSent = Number((row<{ count: number }>("SELECT COUNT(*) AS count FROM sent_messages WHERE LOWER(COALESCE(status, '')) = 'sent'")?.count || 0));
  const departmentsCount = Number((row<{ count: number }>('SELECT COUNT(*) AS count FROM departments WHERE is_active = 1')?.count || 0));

  let studentCount = 0;
  if (user?.role === 'counselor') {
    studentCount = Number((row<{ count: number }>('SELECT COUNT(*) AS count FROM counselor_students WHERE counselor_email = ? AND is_active = 1', [user.email])?.count || 0));
  }

  return { totalUsers, counselorCount, activeSessions, messagesSent, departmentsCount, studentCount };
}

export function getDepartments(activeOnly = true) {
  const query = `
    SELECT id, code, name, color, is_active
    FROM departments
    ${activeOnly ? 'WHERE is_active = 1' : ''}
    ORDER BY code
  `;

  return rows<SqlRow>(query).map((item) => ({
    id: Number(item.id || 0),
    code: String(item.code || ''),
    name: String(item.name || item.code || ''),
    color: String(item.color || '#667eea'),
    is_active: Number(item.is_active || 0),
  }));
}

export function createDepartment(code: string, name: string) {
  const normalizedCode = String(code || '').trim().toUpperCase();
  const normalizedName = String(name || '').trim();
  if (!normalizedCode || !normalizedName) {
    throw new Error('Department code and name are required.');
  }

  db.prepare('INSERT INTO departments (code, name) VALUES (?, ?)').run(normalizedCode, normalizedName);
  return row<SqlRow>('SELECT id, code, name, color, is_active FROM departments WHERE code = ?', [normalizedCode]);
}

export function updateDepartment(id: number, code: string, name: string) {
  const normalizedCode = String(code || '').trim().toUpperCase();
  const normalizedName = String(name || '').trim();
  if (!normalizedCode || !normalizedName) {
    throw new Error('Department code and name are required.');
  }

  db.prepare('UPDATE departments SET code = ?, name = ? WHERE id = ?').run(normalizedCode, normalizedName, id);
  return row<SqlRow>('SELECT id, code, name, color, is_active FROM departments WHERE id = ?', [id]);
}

export function toggleDepartment(id: number) {
  db.prepare(`
    UPDATE departments
    SET is_active = CASE WHEN COALESCE(is_active, 1) = 1 THEN 0 ELSE 1 END
    WHERE id = ?
  `).run(id);
  return row<SqlRow>('SELECT id, code, name, color, is_active FROM departments WHERE id = ?', [id]);
}

export function lockCounselorsForDepartment(departmentCode: string) {
  const normalizedDepartment = String(departmentCode || '').trim().toUpperCase();
  if (!normalizedDepartment) return;
  db.prepare(`
    UPDATE users
    SET is_locked = 1,
        is_active = 0,
        lock_reason = 'department_disabled'
    WHERE LOWER(COALESCE(role, '')) = 'counselor'
      AND UPPER(COALESCE(department, '')) = ?
      AND COALESCE(is_locked, 0) = 0
  `).run(normalizedDepartment);
  db.prepare(`
    UPDATE active_sessions
    SET is_active = 0,
        forced_logout = 1,
        logout_reason = 'department_disabled'
    WHERE user_email IN (
      SELECT email
      FROM users
      WHERE LOWER(COALESCE(role, '')) = 'counselor'
        AND UPPER(COALESCE(department, '')) = ?
    )
      AND is_active = 1
  `).run(normalizedDepartment);
}

export function unlockCounselorsForDepartment(departmentCode: string) {
  const normalizedDepartment = String(departmentCode || '').trim().toUpperCase();
  if (!normalizedDepartment) return;
  db.prepare(`
    UPDATE users
    SET is_locked = 0,
        is_active = 1,
        lock_reason = NULL
    WHERE LOWER(COALESCE(role, '')) = 'counselor'
      AND UPPER(COALESCE(department, '')) = ?
      AND COALESCE(lock_reason, '') = 'department_disabled'
  `).run(normalizedDepartment);
}

export function deleteDepartment(id: number) {
  db.prepare('DELETE FROM departments WHERE id = ?').run(id);
}

export interface SubjectFacultyAllocation {
  faculty_name: string;
  class_sections: string[];
}

function normalizeSubjectFacultyAllocations(
  allocations: Array<{ faculty_name?: string; class_sections?: string[] }> = [],
  fallbackFacultyName = '',
  fallbackClassSections: string[] = [],
) {
  const normalized = allocations
    .map((entry) => ({
      faculty_name: String(entry?.faculty_name || '').trim(),
      class_sections: Array.from(new Set((entry?.class_sections || []).map((value) => String(value || '').trim().toUpperCase()).filter(Boolean))),
    }))
    .filter((entry) => entry.faculty_name);

  if (normalized.length) {
    return normalized;
  }

  const fallbackName = String(fallbackFacultyName || '').trim();
  const fallbackClasses = Array.from(new Set((fallbackClassSections || []).map((value) => String(value || '').trim().toUpperCase()).filter(Boolean)));
  return fallbackName ? [{ faculty_name: fallbackName, class_sections: fallbackClasses }] : [];
}

export interface SubjectRecord {
  id: number;
  subject_code: string;
  subject_name: string;
  faculty_name: string;
  google_sheet_link: string;
  department: string;
  year_level: number;
  semester: string;
  academic_start_year: number | null;
  academic_end_year: number | null;
  class_sections: string[];
  faculty_allocations: SubjectFacultyAllocation[];
  created_at: string | null;
  updated_at: string | null;
}

export interface CdpClassSnapshotRecord {
  label: string;
  total_date_cols: number;
  filled_cols: number;
  completion_pct: number;
  today_col_exists: boolean;
  today_col_filled: boolean;
  pending_dates: string[];
  missing_entry_count: number;
}

export interface CdpFacultySnapshotRecord {
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
}

export interface CdpMarkEntryCellSnapshotRecord {
  status: 'complete' | 'pending' | 'not_available' | 'error';
  filled_students: number;
  total_students: number;
  completion_pct: number;
  pending_students: number;
  message: string;
}

export interface CdpMarkEntryRowSnapshotRecord {
  faculty_name: string;
  class_label: string;
  tests: Record<'iat1' | 'iat2' | 'model' | 'unit_test', CdpMarkEntryCellSnapshotRecord>;
}

export interface CdpMarkEntrySummarySnapshotRecord {
  key: 'iat1' | 'iat2' | 'model' | 'unit_test';
  label: string;
  status: 'complete' | 'pending' | 'not_available' | 'error';
  filled_students: number;
  total_students: number;
  completion_pct: number;
  pending_students: number;
  message: string;
}

export interface CdpMarkEntrySnapshotRecord {
  summaries: CdpMarkEntrySummarySnapshotRecord[];
  rows: CdpMarkEntryRowSnapshotRecord[];
}

export interface CdpSubjectSnapshotRecord {
  subject_id: number;
  department: string;
  year_level: number;
  semester: string;
  summary_status: 'ready' | 'pending' | 'error' | 'unparsed';
  faculty_count: number;
  allocated_class_count: number;
  pending_faculty_count: number;
  pending_class_count: number;
  pending_date_count: number;
  parsed_at: string | null;
  parser_error: string;
  class_statuses: CdpClassSnapshotRecord[];
  faculty_statuses: CdpFacultySnapshotRecord[];
  mark_entry_statuses: CdpMarkEntrySnapshotRecord;
  updated_at: string | null;
}

function mapSubjectRecord(item: SqlRow): SubjectRecord {
  let classSections: string[] = [];
  let facultyAllocations: SubjectFacultyAllocation[] = [];
  try {
    const parsed = JSON.parse(String(item.class_sections || '[]'));
    if (Array.isArray(parsed)) {
      classSections = parsed
        .map((value) => String(value || '').trim().toUpperCase())
        .filter(Boolean);
    }
  } catch {
    classSections = [];
  }
  try {
    const parsed = JSON.parse(String(item.faculty_allocations || '[]'));
    if (Array.isArray(parsed)) {
      facultyAllocations = normalizeSubjectFacultyAllocations(parsed as Array<{ faculty_name?: string; class_sections?: string[] }>);
    }
  } catch {
    facultyAllocations = [];
  }
  facultyAllocations = normalizeSubjectFacultyAllocations(facultyAllocations, String(item.faculty_name || '').trim(), classSections);
  return {
    id: Number(item.id || 0),
    subject_code: String(item.subject_code || '').trim(),
    subject_name: String(item.subject_name || '').trim(),
    faculty_name: String(item.faculty_name || '').trim(),
    google_sheet_link: String(item.google_sheet_link || '').trim(),
    department: String(item.department || '').trim().toUpperCase(),
    year_level: Number(item.year_level || 1),
    semester: String(item.semester || '1').trim() || '1',
    academic_start_year: item.academic_start_year == null ? null : Number(item.academic_start_year),
    academic_end_year: item.academic_end_year == null ? null : Number(item.academic_end_year),
    class_sections: classSections,
    faculty_allocations: facultyAllocations,
    created_at: item.created_at ? String(item.created_at) : null,
    updated_at: item.updated_at ? String(item.updated_at) : null,
  };
}

export function getSubjectById(subjectId: number) {
  const item = row<SqlRow>('SELECT * FROM subjects WHERE id = ?', [Number(subjectId || 0)]);
  return item ? mapSubjectRecord(item) : null;
}

export function listSubjects(options?: {
  department?: string;
  year_level?: number | null;
  semester?: string | null;
}) {
  const where: string[] = [];
  const params: unknown[] = [];

  if (options?.department) {
    where.push('UPPER(COALESCE(department, \'\')) = ?');
    params.push(String(options.department || '').trim().toUpperCase());
  }
  if (options?.year_level) {
    where.push('year_level = ?');
    params.push(Number(options.year_level || 1));
  }
  if (options?.semester) {
    where.push('semester = ?');
    params.push(String(options.semester || '1').trim());
  }

  const query = `
    SELECT *
    FROM subjects
    ${where.length ? `WHERE ${where.join(' AND ')}` : ''}
    ORDER BY UPPER(COALESCE(subject_code, '')), UPPER(COALESCE(subject_name, '')), id DESC
  `;

  return rows<SqlRow>(query, params).map(mapSubjectRecord);
}

export function listSubjectsForActor(
  actor: AuthUser,
  options?: {
    department?: string;
    year_level?: number | null;
    semester?: string | null;
  },
) {
  const allSubjects = listSubjects(options);
  if (actor.role === 'admin' || actor.role === 'principal') return allSubjects;

  const allowed = new Set(actor.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
  return allSubjects.filter((subject) => allowed.has(`${subject.department.toUpperCase()}::${subject.year_level}`));
}

export function createSubjectRecord(payload: {
  subject_code: string;
  subject_name: string;
  faculty_name: string;
  google_sheet_link?: string;
  department: string;
  year_level: number;
  semester: string;
  academic_start_year?: number | null;
  academic_end_year?: number | null;
  class_sections?: string[];
  faculty_allocations?: SubjectFacultyAllocation[];
}) {
  const subjectCode = String(payload.subject_code || '').trim().toUpperCase();
  const subjectName = String(payload.subject_name || '').trim();
  const googleSheetLink = String(payload.google_sheet_link || '').trim();
  const department = String(payload.department || '').trim().toUpperCase();
  const yearLevel = Number(payload.year_level || 1);
  const semester = String(payload.semester || '1').trim() || '1';
  const academicStartYear = payload.academic_start_year == null ? null : Number(payload.academic_start_year);
  const academicEndYear = payload.academic_end_year == null ? null : Number(payload.academic_end_year);
  const facultyAllocations = normalizeSubjectFacultyAllocations(payload.faculty_allocations, payload.faculty_name, payload.class_sections || []);
  const facultyName = facultyAllocations.map((entry) => entry.faculty_name).join(' / ');
  const classSections = Array.from(new Set(facultyAllocations.flatMap((entry) => entry.class_sections)));

  if (!subjectCode || !subjectName || !facultyName || !department || ![1, 2, 3, 4].includes(yearLevel) || !['1', '2'].includes(semester)) {
    throw new Error('Subject code, name, faculty, department, year, and semester are required.');
  }
  if (!academicStartYear || !academicEndYear || academicStartYear < 2000 || academicEndYear < academicStartYear || academicEndYear > academicStartYear + 1) {
    throw new Error('Provide a valid academic start/end year range like 2025 and 2026, or use the same year for both fields when the sheet stays in one calendar year.');
  }
  if (!classSections.length) {
    throw new Error('Select at least one allocated class for this subject.');
  }

  const info = db.prepare(`
    INSERT INTO subjects (
      subject_code, subject_name, faculty_name, google_sheet_link, department, year_level, semester, academic_start_year, academic_end_year, class_sections, faculty_allocations, created_at, updated_at
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP, CURRENT_TIMESTAMP)
  `).run(subjectCode, subjectName, facultyName, googleSheetLink, department, yearLevel, semester, academicStartYear, academicEndYear, JSON.stringify(classSections), JSON.stringify(facultyAllocations));

  return getSubjectById(Number(info.lastInsertRowid || 0));
}

export function updateSubjectRecord(subjectId: number, payload: {
  subject_code: string;
  subject_name: string;
  faculty_name: string;
  google_sheet_link?: string;
  semester: string;
  academic_start_year?: number | null;
  academic_end_year?: number | null;
  class_sections?: string[];
  faculty_allocations?: SubjectFacultyAllocation[];
}) {
  const subjectCode = String(payload.subject_code || '').trim().toUpperCase();
  const subjectName = String(payload.subject_name || '').trim();
  const googleSheetLink = String(payload.google_sheet_link || '').trim();
  const semester = String(payload.semester || '1').trim() || '1';
  const academicStartYear = payload.academic_start_year == null ? null : Number(payload.academic_start_year);
  const academicEndYear = payload.academic_end_year == null ? null : Number(payload.academic_end_year);
  const facultyAllocations = normalizeSubjectFacultyAllocations(payload.faculty_allocations, payload.faculty_name, payload.class_sections || []);
  const facultyName = facultyAllocations.map((entry) => entry.faculty_name).join(' / ');
  const classSections = Array.from(new Set(facultyAllocations.flatMap((entry) => entry.class_sections)));

  if (!subjectCode || !subjectName || !facultyName || !['1', '2'].includes(semester)) {
    throw new Error('Subject code, name, faculty, and semester are required.');
  }
  if (!academicStartYear || !academicEndYear || academicStartYear < 2000 || academicEndYear < academicStartYear || academicEndYear > academicStartYear + 1) {
    throw new Error('Provide a valid academic start/end year range like 2025 and 2026, or use the same year for both fields when the sheet stays in one calendar year.');
  }
  if (!classSections.length) {
    throw new Error('Select at least one allocated class for this subject.');
  }

  db.prepare(`
    UPDATE subjects
    SET subject_code = ?,
        subject_name = ?,
        faculty_name = ?,
        google_sheet_link = ?,
        semester = ?,
        academic_start_year = ?,
        academic_end_year = ?,
        class_sections = ?,
        faculty_allocations = ?,
        updated_at = CURRENT_TIMESTAMP
    WHERE id = ?
  `).run(subjectCode, subjectName, facultyName, googleSheetLink, semester, academicStartYear, academicEndYear, JSON.stringify(classSections), JSON.stringify(facultyAllocations), Number(subjectId || 0));

  return getSubjectById(subjectId);
}

export function deleteSubjectRecord(subjectId: number) {
  db.prepare('DELETE FROM subjects WHERE id = ?').run(Number(subjectId || 0));
}

function parseJsonArray<T>(value: unknown): T[] {
  try {
    const parsed = JSON.parse(String(value || '[]'));
    return Array.isArray(parsed) ? (parsed as T[]) : [];
  } catch {
    return [];
  }
}

function mapCdpSubjectSnapshotRecord(item: SqlRow): CdpSubjectSnapshotRecord {
  const classStatuses = parseJsonArray<CdpClassSnapshotRecord>(item.class_statuses).map((entry) => ({
    label: String(entry?.label || '').trim(),
    total_date_cols: Number(entry?.total_date_cols || 0),
    filled_cols: Number(entry?.filled_cols || 0),
    completion_pct: Number(entry?.completion_pct || 0),
    today_col_exists: !!entry?.today_col_exists,
    today_col_filled: !!entry?.today_col_filled,
    pending_dates: Array.isArray(entry?.pending_dates) ? entry.pending_dates.map((value) => String(value || '').trim()).filter(Boolean) : [],
    missing_entry_count: Number(entry?.missing_entry_count || 0),
  })).filter((entry) => entry.label);
  const facultyStatuses = parseJsonArray<CdpFacultySnapshotRecord>(item.faculty_statuses).map((entry) => {
    const statusValue: CdpFacultySnapshotRecord['status'] = entry?.status === 'error' ? 'error' : entry?.status === 'pending' ? 'pending' : 'ready';
    return {
      faculty_name: String(entry?.faculty_name || '').trim(),
      class_sections: Array.isArray(entry?.class_sections) ? entry.class_sections.map((value) => String(value || '').trim().toUpperCase()).filter(Boolean) : [],
      status: statusValue,
      filled_cols: Number(entry?.filled_cols || 0),
      total_date_cols: Number(entry?.total_date_cols || 0),
      completion_pct: Number(entry?.completion_pct || 0),
      pending_class_count: Number(entry?.pending_class_count || 0),
      pending_dates: Array.isArray(entry?.pending_dates) ? entry.pending_dates.map((value) => String(value || '').trim()).filter(Boolean) : [],
      pending_classes: Array.isArray(entry?.pending_classes) ? entry.pending_classes.map((value) => String(value || '').trim().toUpperCase()).filter(Boolean) : [],
      missing_entry_count: Number(entry?.missing_entry_count || 0),
      class_breakdown: Array.isArray(entry?.class_breakdown)
        ? entry.class_breakdown.map((item) => ({
          class_label: String(item?.class_label || '').trim().toUpperCase(),
          filled_cols: Number(item?.filled_cols || 0),
          total_date_cols: Number(item?.total_date_cols || 0),
          completion_pct: Number(item?.completion_pct || 0),
          pending_dates: Array.isArray(item?.pending_dates) ? item.pending_dates.map((value) => String(value || '').trim()).filter(Boolean) : [],
          missing_entry_count: Number(item?.missing_entry_count || 0),
        })).filter((item) => item.class_label)
        : [],
      notes: Array.isArray(entry?.notes) ? entry.notes.map((value) => String(value || '').trim()).filter(Boolean) : [],
    };
  }).filter((entry) => entry.faculty_name);
  let markEntryStatuses: CdpMarkEntrySnapshotRecord = {
    summaries: [],
    rows: [],
  };
  try {
    const parsed = JSON.parse(String(item.mark_entry_statuses || '{}')) as {
      summaries?: Array<Partial<CdpMarkEntrySummarySnapshotRecord>>;
      rows?: Array<{
        faculty_name?: string;
        class_label?: string;
        tests?: Partial<Record<'iat1' | 'iat2' | 'model' | 'unit_test', Partial<CdpMarkEntryCellSnapshotRecord>>>;
      }>;
    };
    const normalizeCell = (entry?: Partial<CdpMarkEntryCellSnapshotRecord>): CdpMarkEntryCellSnapshotRecord => {
      const status =
        entry?.status === 'complete'
        || entry?.status === 'pending'
        || entry?.status === 'error'
          ? entry.status
          : 'not_available';
      return {
        status,
        filled_students: Number(entry?.filled_students || 0),
        total_students: Number(entry?.total_students || 0),
        completion_pct: Number(entry?.completion_pct || 0),
        pending_students: Number(entry?.pending_students || 0),
        message: String(entry?.message || '').trim(),
      };
    };
    markEntryStatuses = {
      summaries: Array.isArray(parsed?.summaries)
        ? parsed.summaries
          .map((entry) => {
            const key =
              entry?.key === 'iat1'
              || entry?.key === 'iat2'
              || entry?.key === 'model'
              || entry?.key === 'unit_test'
                ? entry.key
                : null;
            if (!key) return null;
            return {
              key,
              label: String(entry?.label || '').trim() || key.toUpperCase(),
              ...normalizeCell(entry),
            };
          })
          .filter((entry): entry is CdpMarkEntrySummarySnapshotRecord => !!entry)
        : [],
      rows: Array.isArray(parsed?.rows)
        ? parsed.rows
          .map((entry) => {
            const facultyName = String(entry?.faculty_name || '').trim();
            const classLabel = String(entry?.class_label || '').trim().toUpperCase();
            if (!facultyName || !classLabel) return null;
            const tests = entry?.tests || {};
            return {
              faculty_name: facultyName,
              class_label: classLabel,
              tests: {
                iat1: normalizeCell(tests.iat1),
                iat2: normalizeCell(tests.iat2),
                model: normalizeCell(tests.model),
                unit_test: normalizeCell(tests.unit_test),
              },
            };
          })
          .filter((entry): entry is CdpMarkEntryRowSnapshotRecord => !!entry)
        : [],
    };
  } catch {
    markEntryStatuses = {
      summaries: [],
      rows: [],
    };
  }
  const summaryStatus = String(item.summary_status || '').trim().toLowerCase();
  return {
    subject_id: Number(item.subject_id || 0),
    department: String(item.department || '').trim().toUpperCase(),
    year_level: Number(item.year_level || 1),
    semester: String(item.semester || '1').trim() || '1',
    summary_status: summaryStatus === 'ready' || summaryStatus === 'pending' || summaryStatus === 'error' ? summaryStatus : 'unparsed',
    faculty_count: Number(item.faculty_count || 0),
    allocated_class_count: Number(item.allocated_class_count || 0),
    pending_faculty_count: Number(item.pending_faculty_count || 0),
    pending_class_count: Number(item.pending_class_count || 0),
    pending_date_count: Number(item.pending_date_count || 0),
    parsed_at: item.parsed_at ? String(item.parsed_at) : null,
    parser_error: String(item.parser_error || '').trim(),
    class_statuses: classStatuses,
    faculty_statuses: facultyStatuses,
    mark_entry_statuses: markEntryStatuses,
    updated_at: item.updated_at ? String(item.updated_at) : null,
  };
}

export function getCdpSubjectSnapshot(subjectId: number) {
  const item = row<SqlRow>('SELECT * FROM cdp_subject_snapshots WHERE subject_id = ?', [Number(subjectId || 0)]);
  return item ? mapCdpSubjectSnapshotRecord(item) : null;
}

export function listCdpSubjectSnapshots(options?: {
  department?: string;
  year_level?: number | null;
  semester?: string | null;
  subjectIds?: number[];
}) {
  const where: string[] = [];
  const params: unknown[] = [];

  if (options?.department) {
    where.push('UPPER(COALESCE(department, \'\')) = ?');
    params.push(String(options.department || '').trim().toUpperCase());
  }
  if (options?.year_level) {
    where.push('year_level = ?');
    params.push(Number(options.year_level || 1));
  }
  if (options?.semester) {
    where.push('semester = ?');
    params.push(String(options.semester || '1').trim());
  }
  if (options?.subjectIds?.length) {
    const ids = Array.from(new Set(options.subjectIds.map((value) => Number(value || 0)).filter((value) => value > 0)));
    if (ids.length) {
      where.push(`subject_id IN (${ids.map(() => '?').join(', ')})`);
      params.push(...ids);
    }
  }

  const query = `
    SELECT *
    FROM cdp_subject_snapshots
    ${where.length ? `WHERE ${where.join(' AND ')}` : ''}
    ORDER BY department, year_level, semester, subject_id
  `;

  return rows<SqlRow>(query, params).map(mapCdpSubjectSnapshotRecord);
}

export function upsertCdpSubjectSnapshot(payload: {
  subject_id: number;
  department: string;
  year_level: number;
  semester: string;
  summary_status: 'ready' | 'pending' | 'error' | 'unparsed';
  faculty_count: number;
  allocated_class_count: number;
  pending_faculty_count: number;
  pending_class_count: number;
  pending_date_count: number;
  parsed_at?: string | null;
  parser_error?: string;
  class_statuses?: CdpClassSnapshotRecord[];
  faculty_statuses?: CdpFacultySnapshotRecord[];
  mark_entry_statuses?: CdpMarkEntrySnapshotRecord;
}) {
  const subjectId = Number(payload.subject_id || 0);
  if (!subjectId) throw new Error('Subject snapshot subject id is required.');
  db.prepare(`
    INSERT INTO cdp_subject_snapshots (
      subject_id, department, year_level, semester, summary_status, faculty_count, allocated_class_count, pending_faculty_count,
      pending_class_count, pending_date_count, parsed_at, parser_error, class_statuses, faculty_statuses, mark_entry_statuses, updated_at
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
    ON CONFLICT(subject_id) DO UPDATE SET
      department = excluded.department,
      year_level = excluded.year_level,
      semester = excluded.semester,
      summary_status = excluded.summary_status,
      faculty_count = excluded.faculty_count,
      allocated_class_count = excluded.allocated_class_count,
      pending_faculty_count = excluded.pending_faculty_count,
      pending_class_count = excluded.pending_class_count,
      pending_date_count = excluded.pending_date_count,
      parsed_at = excluded.parsed_at,
      parser_error = excluded.parser_error,
      class_statuses = excluded.class_statuses,
      faculty_statuses = excluded.faculty_statuses,
      mark_entry_statuses = excluded.mark_entry_statuses,
      updated_at = CURRENT_TIMESTAMP
  `).run(
    subjectId,
    String(payload.department || '').trim().toUpperCase(),
    Number(payload.year_level || 1),
    String(payload.semester || '1').trim() || '1',
    payload.summary_status || 'unparsed',
    Number(payload.faculty_count || 0),
    Number(payload.allocated_class_count || 0),
    Number(payload.pending_faculty_count || 0),
    Number(payload.pending_class_count || 0),
    Number(payload.pending_date_count || 0),
    payload.parsed_at ? String(payload.parsed_at) : null,
    String(payload.parser_error || '').trim(),
    JSON.stringify(payload.class_statuses || []),
    JSON.stringify(payload.faculty_statuses || []),
    JSON.stringify(payload.mark_entry_statuses || { summaries: [], rows: [] }),
  );

  return getCdpSubjectSnapshot(subjectId);
}

export function deleteCdpSubjectSnapshot(subjectId: number) {
  db.prepare('DELETE FROM cdp_subject_snapshots WHERE subject_id = ?').run(Number(subjectId || 0));
}

export function getSubjectScopeSnapshot(department: string, yearLevel: number) {
  const normalizedDepartment = String(department || '').trim().toUpperCase();
  const normalizedYearLevel = Number(yearLevel || 1);

  const counselorCount = Number(
    row<{ count: number }>(
      `
        SELECT COUNT(*) AS count
        FROM users
        WHERE LOWER(COALESCE(role, '')) = 'counselor'
          AND UPPER(COALESCE(department, '')) = ?
          AND year_level = ?
      `,
      [normalizedDepartment, normalizedYearLevel],
    )?.count || 0,
  );

  const studentCount = Number(
    row<{ count: number }>(
      `
        SELECT COUNT(*) AS count
        FROM counselor_students cs
        INNER JOIN users u ON LOWER(COALESCE(u.email, '')) = LOWER(COALESCE(cs.counselor_email, ''))
        WHERE LOWER(COALESCE(u.role, '')) = 'counselor'
          AND UPPER(COALESCE(u.department, '')) = ?
          AND u.year_level = ?
      `,
      [normalizedDepartment, normalizedYearLevel],
    )?.count || 0,
  );

  return {
    department: normalizedDepartment,
    year_level: normalizedYearLevel,
    counselor_count: counselorCount,
    student_count: studentCount,
  };
}

export function getUsersForActor(actor: AuthUser) {
  const allUsers = rows<SqlRow>('SELECT * FROM users ORDER BY created_at DESC');
  if (actor.role === 'admin' || actor.role === 'principal') return allUsers;
  if (actor.role !== 'deo') return [];

  const allowed = new Set(actor.scopes.map((scope) => `${scope.department}::${scope.year_level}`));
  return allUsers.filter((item) => {
    const role = normalizeRole(item.role);
    if (role !== 'counselor') return false;
    return allowed.has(`${String(item.department || '').toUpperCase()}::${Number(item.year_level || 1)}`);
  });
}

export function listUsersForActor(actor: AuthUser) {
  return getUsersForActor(actor).map((item) => ({
    account_email: String(item.email || ''),
    email: getUserLoginEmailValue(item) || String(item.email || ''),
    name: String(item.name || item.email || ''),
    role: normalizeRole(item.role),
    designation: normalizeRole(item.role) === 'principal' ? String(item.designation || '').trim() : '',
    department: item.department ? String(item.department) : null,
    year_level: Number(item.year_level || 1),
    is_active: Number(item.is_active || 0),
    is_locked: Number(item.is_locked || 0),
    created_at: item.created_at ? String(item.created_at) : null,
    max_students: Number(item.max_students || 0),
    scopes: ['hod', 'deo'].includes(normalizeRole(item.role)) ? getScopesForUser(String(item.email || '')) : [],
    student_count:
      normalizeRole(item.role) === 'counselor'
        ? Number(row<{ count: number }>('SELECT COUNT(*) AS count FROM counselor_students WHERE counselor_email = ?', [String(item.email || '').toLowerCase()])?.count || 0)
        : 0,
  }));
}

export interface SessionMonitoringRecord {
  session_id: string;
  user_email: string;
  login_email: string;
  name: string;
  role: string;
  department: string;
  auth_method: string;
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
  login_email: string;
  name: string;
  role: string;
  department: string;
  auth_method: string;
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

export interface AdminMessageRecord extends CounselorMessageRecord {
  counselor_name: string;
}

export interface MessageDayRecord {
  day: string;
  total: number;
  counselors: number;
}

export interface MessageCounselorSuggestion {
  name: string;
  email: string;
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

export interface CounselorActivityScopeSnapshot {
  department: string;
  year_level: number;
  test_status: Record<string, Record<string, boolean>>;
  results: CounselorActivityResult[];
}

export interface CounselorActivitySummaryRow {
  email: string;
  name: string;
  department: string;
  year_level: number;
  last_login: string;
  last_activity: string;
  student_count: number;
  students_with_phone: number;
  tests_uploaded: number;
  total_messages: number;
  week_messages: number;
  unique_students_messaged: number;
  work_status: 'Complete' | 'Partial - No Reports Sent' | 'Partial - No Tests Uploaded' | 'Not Started';
  completion_pct: number;
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
  public_url?: string;
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

function normalizeNoticeScopePairs(scopePairs: Array<{ department: string; year_level: number }>) {
  const seen = new Set<string>();
  const result: NoticeScopePair[] = [];
  for (const pair of scopePairs || []) {
    const department = String(pair.department || '').trim().toUpperCase();
    const yearLevel = Number(pair.year_level || 0) || 0;
    if (!department || ![1, 2, 3, 4].includes(yearLevel)) continue;
    const key = `${department}::${yearLevel}`;
    if (seen.has(key)) continue;
    seen.add(key);
    result.push({ department, year_level: yearLevel });
  }
  return result.sort((a, b) => a.department.localeCompare(b.department) || a.year_level - b.year_level);
}

function getActorNoticeScopeSet(actor: AuthUser | null) {
  if (!actor) return new Set<string>();
  if (actor.role === 'admin' || actor.role === 'principal') return null;
  if (actor.role === 'hod' || actor.role === 'deo') {
    return new Set(actor.scopes.map((scope) => `${scope.department.toUpperCase()}::${scope.year_level}`));
  }
  if (actor.role === 'counselor') {
    return new Set([`${String(actor.department || '').trim().toUpperCase()}::${Number(actor.year_level || 1)}`]);
  }
  return new Set<string>();
}

function formatNoticeDay(value: string) {
  const date = new Date(String(value || '').replace(' ', 'T'));
  if (!Number.isFinite(date.getTime())) return '';
  return date
    .toLocaleDateString('en-GB', {
      day: '2-digit',
      month: 'short',
      year: 'numeric',
    })
    .replace(',', '');
}

function getNoticeTitleDisplay(row: SqlRow) {
  const title = String(row.title || '').trim();
  const text = String(row.message_text || '').trim();
  if (title) return title;
  if (text) return `${text.slice(0, 72)}${text.length > 72 ? '...' : ''}`;
  return `Notice #${Number(row.id || 0)}`;
}

function getNoticeMessagePreview(row: SqlRow) {
  const text = String(row.message_text || '').trim();
  if (!text) return '';
  return `${text.slice(0, 120)}${text.length > 120 ? '...' : ''}`;
}

export function getNotice(noticeId: number) {
  return row<SqlRow>('SELECT * FROM notices WHERE id = ?', [noticeId]);
}

export function getNoticeScopePairs(noticeId: number) {
  return rows<SqlRow>(
    'SELECT department, year_level FROM notice_scopes WHERE notice_id = ? ORDER BY department, year_level',
    [noticeId],
  ).map((item) => ({
    department: String(item.department || '').trim().toUpperCase(),
    year_level: Number(item.year_level || 1),
  } satisfies NoticeScopePair));
}

export function getNoticeAttachments(noticeId: number) {
  return rows<SqlRow>(
    'SELECT * FROM notice_attachments WHERE notice_id = ? ORDER BY id',
    [noticeId],
  ).map((item) => ({
    id: Number(item.id || 0),
    notice_id: Number(item.notice_id || 0),
    original_name: String(item.original_name || item.stored_name || ''),
    relative_path: String(item.relative_path || ''),
    mime_type: String(item.mime_type || ''),
    file_size: Number(item.file_size || 0),
    public_token: String(item.public_token || ''),
  } satisfies NoticeAttachmentRecord));
}

export function getNoticeAttachmentByToken(token: string) {
  const found = row<SqlRow>('SELECT * FROM notice_attachments WHERE public_token = ? LIMIT 1', [String(token || '').trim()]);
  if (!found) return null;
  return {
    id: Number(found.id || 0),
    notice_id: Number(found.notice_id || 0),
    original_name: String(found.original_name || found.stored_name || ''),
    relative_path: String(found.relative_path || ''),
    mime_type: String(found.mime_type || ''),
    file_size: Number(found.file_size || 0),
    public_token: String(found.public_token || ''),
  } satisfies NoticeAttachmentRecord;
}

export function createNotice(
  title: string,
  messageText: string,
  sendToAll: boolean,
  createdBy: string,
  createdRole: string,
  scopePairs: Array<{ department: string; year_level: number }>,
) {
  const cleanedScopes = sendToAll ? [] : normalizeNoticeScopePairs(scopePairs);
  const info = db
    .prepare(
      `
        INSERT INTO notices (title, message_text, send_to_all, created_by, created_role, public_token)
        VALUES (?, ?, ?, ?, ?, ?)
      `,
    )
    .run(
      String(title || '').trim(),
      String(messageText || '').trim(),
      sendToAll ? 1 : 0,
      String(createdBy || '').trim().toLowerCase(),
      String(createdRole || '').trim().toLowerCase(),
      randomUUID().replace(/-/g, ''),
    );

  const noticeId = Number(info.lastInsertRowid || 0);
  for (const scope of cleanedScopes) {
    db.prepare('INSERT OR IGNORE INTO notice_scopes (notice_id, department, year_level) VALUES (?, ?, ?)').run(
      noticeId,
      scope.department,
      scope.year_level,
    );
  }
  return noticeId;
}

export function updateNotice(
  noticeId: number,
  title: string,
  messageText: string,
  sendToAll: boolean,
  scopePairs: Array<{ department: string; year_level: number }>,
) {
  const cleanedScopes = sendToAll ? [] : normalizeNoticeScopePairs(scopePairs);
  db.prepare(
    `
      UPDATE notices
      SET title = ?, message_text = ?, send_to_all = ?, updated_at = CURRENT_TIMESTAMP
      WHERE id = ?
    `,
  ).run(String(title || '').trim(), String(messageText || '').trim(), sendToAll ? 1 : 0, noticeId);
  db.prepare('DELETE FROM notice_scopes WHERE notice_id = ?').run(noticeId);
  for (const scope of cleanedScopes) {
    db.prepare('INSERT OR IGNORE INTO notice_scopes (notice_id, department, year_level) VALUES (?, ?, ?)').run(
      noticeId,
      scope.department,
      scope.year_level,
    );
  }
}

export function addNoticeAttachment(
  noticeId: number,
  storedName: string,
  originalName: string,
  relativePath: string,
  mimeType: string,
  fileSize: number,
) {
  const token = randomUUID().replace(/-/g, '');
  const info = db
    .prepare(
      `
        INSERT INTO notice_attachments
        (notice_id, stored_name, original_name, relative_path, mime_type, file_size, public_token)
        VALUES (?, ?, ?, ?, ?, ?, ?)
      `,
    )
    .run(noticeId, storedName, originalName, relativePath, mimeType || '', Number(fileSize || 0), token);

  return {
    id: Number(info.lastInsertRowid || 0),
    notice_id: noticeId,
    original_name: originalName,
    relative_path: relativePath,
    mime_type: mimeType || '',
    file_size: Number(fileSize || 0),
    public_token: token,
  } satisfies NoticeAttachmentRecord;
}

export function deleteNoticeAttachment(attachmentId: number) {
  const attachment = row<SqlRow>('SELECT * FROM notice_attachments WHERE id = ?', [attachmentId]);
  if (!attachment) return null;
  db.prepare('DELETE FROM notice_attachments WHERE id = ?').run(attachmentId);
  return {
    id: Number(attachment.id || 0),
    notice_id: Number(attachment.notice_id || 0),
    original_name: String(attachment.original_name || attachment.stored_name || ''),
    relative_path: String(attachment.relative_path || ''),
    mime_type: String(attachment.mime_type || ''),
    file_size: Number(attachment.file_size || 0),
    public_token: String(attachment.public_token || ''),
  } satisfies NoticeAttachmentRecord;
}

export function deleteNotice(noticeId: number) {
  const attachments = getNoticeAttachments(noticeId);
  db.prepare('DELETE FROM notices WHERE id = ?').run(noticeId);
  return attachments;
}

function getCounselorRoster() {
  const studentCountMap = new Map<string, number>();
  for (const rowItem of rows<SqlRow>(
    `
      SELECT counselor_email, COUNT(*) AS student_count
      FROM counselor_students
      WHERE COALESCE(is_active, 1) = 1
      GROUP BY counselor_email
    `,
  )) {
    studentCountMap.set(String(rowItem.counselor_email || '').trim().toLowerCase(), Number(rowItem.student_count || 0));
  }

  const messageCountMap = new Map<string, number>();
  for (const rowItem of rows<SqlRow>(
    `
      SELECT counselor_email, COUNT(*) AS message_count
      FROM notice_deliveries
      GROUP BY counselor_email
    `,
  )) {
    messageCountMap.set(String(rowItem.counselor_email || '').trim().toLowerCase(), Number(rowItem.message_count || 0));
  }

  return rows<SqlRow>(
    "SELECT email, name, department, year_level FROM users WHERE LOWER(role) = 'counselor' ORDER BY department, year_level, name",
  ).map((item) => {
    const email = String(item.email || '').trim().toLowerCase();
    return {
      email,
      name: String(item.name || email),
      department: String(item.department || '').trim().toUpperCase(),
      year_level: Number(item.year_level || 1),
      student_count: Number(studentCountMap.get(email) || 0),
      message_count: Number(messageCountMap.get(email) || 0),
    };
  });
}

function matchesActorNoticeScope(actorScopes: Set<string> | null, noticeSendToAll: boolean, scopePairs: NoticeScopePair[]) {
  if (actorScopes === null) return true;
  if (noticeSendToAll) return actorScopes.size > 0;
  return scopePairs.some((pair) => actorScopes.has(`${pair.department}::${pair.year_level}`));
}

function matchesNoticeFilters(
  noticeSendToAll: boolean,
  scopePairs: NoticeScopePair[],
  filterDepartment?: string | null,
  filterYearLevel?: number | null,
) {
  const dep = String(filterDepartment || '').trim().toUpperCase();
  const year = Number(filterYearLevel || 0) || null;
  if (!dep && !year) return true;
  if (noticeSendToAll) return true;
  return scopePairs.some((pair) => (!dep || pair.department === dep) && (!year || pair.year_level === year));
}

function buildNoticeSummaryRow(
  notice: SqlRow,
  scopePairs: NoticeScopePair[],
  attachments: NoticeAttachmentRecord[],
  counselors: ReturnType<typeof getCounselorRoster>,
  actor: AuthUser,
) {
  const noticeId = Number(notice.id || 0);
  const sendToAll = Boolean(Number(notice.send_to_all || 0));
  const deliveryCountMap = new Map<string, number>();
  for (const delivery of rows<SqlRow>(
    `
      SELECT counselor_email, COUNT(*) AS sent_count
      FROM notice_deliveries
      WHERE notice_id = ?
      GROUP BY counselor_email
    `,
    [noticeId],
  )) {
    deliveryCountMap.set(String(delivery.counselor_email || '').trim().toLowerCase(), Number(delivery.sent_count || 0));
  }

  const relevantCounselors = counselors.filter((counselor) => {
    if (sendToAll) return true;
    return scopePairs.some((pair) => pair.department === counselor.department && pair.year_level === counselor.year_level);
  });

  let completedCounselors = 0;
  let sentStudents = 0;
  let totalStudents = 0;
  for (const counselor of relevantCounselors) {
    const sentCount = Math.min(counselor.student_count, Number(deliveryCountMap.get(counselor.email) || 0));
    sentStudents += sentCount;
    totalStudents += counselor.student_count;
    if (counselor.student_count > 0 && sentCount >= counselor.student_count) completedCounselors += 1;
  }

  const actorScopeSet = getActorNoticeScopeSet(actor);
  const canManageFully =
    actor.role === 'admin' ||
    actor.role === 'principal' ||
    (!sendToAll &&
      actorScopeSet !== null &&
      scopePairs.length > 0 &&
      scopePairs.every((pair) => actorScopeSet.has(`${pair.department}::${pair.year_level}`)));

  return {
    id: noticeId,
    title: String(notice.title || '').trim(),
    message_text: String(notice.message_text || '').trim(),
    title_display: getNoticeTitleDisplay(notice),
    message_preview: getNoticeMessagePreview(notice),
    send_to_all: sendToAll ? 1 : 0,
    created_by: String(notice.created_by || '').trim().toLowerCase(),
    created_role: String(notice.created_role || '').trim().toLowerCase(),
    created_at: String(notice.created_at || ''),
    created_day: formatNoticeDay(String(notice.created_at || '')),
    created_by_name: String(
      row<SqlRow>('SELECT name FROM users WHERE email = ? LIMIT 1', [String(notice.created_by || '').trim().toLowerCase()])?.name ||
        notice.created_by ||
        '',
    ),
    attachment_count: attachments.length,
    attachments,
    scope_pairs: scopePairs,
    scope_labels: sendToAll ? ['All Departments / All Years'] : scopePairs.map((pair) => `${pair.department} - Y${pair.year_level}`),
    completion_status:
      relevantCounselors.length > 0 && completedCounselors >= relevantCounselors.length ? 'completed' : 'pending',
    completed_counselors: completedCounselors,
    total_counselors: relevantCounselors.length,
    sent_students: sentStudents,
    total_students: totalStudents,
    can_manage_fully: canManageFully,
  } satisfies NoticeRecord;
}

export function getNoticeRecordsForActor(
  actor: AuthUser,
  options?: {
    filterDepartment?: string | null;
    filterYearLevel?: number | null;
    filterStatus?: string | null;
    filterDateFrom?: string | null;
    filterDateTo?: string | null;
  },
) {
  const actorScopeSet = getActorNoticeScopeSet(actor);
  const filterDepartment = String(options?.filterDepartment || '').trim().toUpperCase();
  const filterYearLevel = Number(options?.filterYearLevel || 0) || null;
  const filterStatus = String(options?.filterStatus || '').trim().toLowerCase();
  const filterDateFrom = String(options?.filterDateFrom || '').trim();
  const filterDateTo = String(options?.filterDateTo || '').trim();
  const notices = rows<SqlRow>('SELECT * FROM notices ORDER BY created_at DESC, id DESC');
  const counselors = getCounselorRoster().filter((counselor) => {
    if (actorScopeSet === null) return true;
    return actorScopeSet.has(`${counselor.department}::${counselor.year_level}`);
  });

  const results: NoticeRecord[] = [];
  for (const notice of notices) {
    const scopePairs = getNoticeScopePairs(Number(notice.id || 0));
    const sendToAll = Boolean(Number(notice.send_to_all || 0));
    if (!matchesActorNoticeScope(actorScopeSet, sendToAll, scopePairs)) continue;
    if (!matchesNoticeFilters(sendToAll, scopePairs, filterDepartment, filterYearLevel)) continue;

    const createdAt = String(notice.created_at || '').slice(0, 10);
    if (filterDateFrom && createdAt && createdAt < filterDateFrom) continue;
    if (filterDateTo && createdAt && createdAt > filterDateTo) continue;

    const record = buildNoticeSummaryRow(notice, scopePairs, getNoticeAttachments(Number(notice.id || 0)), counselors, actor);
    if (filterStatus && record.completion_status !== filterStatus) continue;
    results.push(record);
  }
  return results;
}

export function getNoticeCompletionRows(actor: AuthUser) {
  const actorScopeSet = getActorNoticeScopeSet(actor);
  const counselors = getCounselorRoster().filter((counselor) => {
    if (actorScopeSet === null) return true;
    return actorScopeSet.has(`${counselor.department}::${counselor.year_level}`);
  });
  const notices = rows<SqlRow>('SELECT * FROM notices ORDER BY created_at DESC, id DESC');

  return counselors
    .map((counselor) => {
      const pendingTitles: string[] = [];
      let totalNoticeCount = 0;
      let completedNoticeCount = 0;

      for (const notice of notices) {
        const scopePairs = getNoticeScopePairs(Number(notice.id || 0));
        const sendToAll = Boolean(Number(notice.send_to_all || 0));
        if (!sendToAll && !scopePairs.some((pair) => pair.department === counselor.department && pair.year_level === counselor.year_level)) {
          continue;
        }
        totalNoticeCount += 1;
        const sentCount = Number(
          row<SqlRow>(
            'SELECT COUNT(*) AS sent_count FROM notice_deliveries WHERE notice_id = ? AND counselor_email = ?',
            [Number(notice.id || 0), counselor.email],
          )?.sent_count || 0,
        );
        if (counselor.student_count > 0 && sentCount >= counselor.student_count) {
          completedNoticeCount += 1;
        } else {
          pendingTitles.push(getNoticeTitleDisplay(notice));
        }
      }

      let completionState: NoticeCompletionRow['completion_state'] = 'pending';
      if (totalNoticeCount <= 0) completionState = 'no_notices';
      else if (counselor.student_count <= 0) completionState = 'no_students';
      else if (!pendingTitles.length) completionState = 'completed';

      return {
        email: counselor.email,
        name: counselor.name,
        department: counselor.department,
        year_level: counselor.year_level,
        student_count: counselor.student_count,
        message_count: counselor.message_count,
        total_notice_count: totalNoticeCount,
        completed_notice_count: completedNoticeCount,
        pending_notice_count: pendingTitles.length,
        pending_notice_titles: pendingTitles,
        completion_state: completionState,
        completion_pct: totalNoticeCount > 0 ? Math.round((completedNoticeCount / totalNoticeCount) * 1000) / 10 : 0,
      } satisfies NoticeCompletionRow;
    })
    .sort((a, b) => {
      if (b.pending_notice_count !== a.pending_notice_count) return b.pending_notice_count - a.pending_notice_count;
      return a.name.localeCompare(b.name);
    });
}

export function getVisibleNoticesForCounselor(
  counselorEmail: string,
  options?: {
    filterStatus?: string | null;
    filterDateFrom?: string | null;
    filterDateTo?: string | null;
  },
) {
  const counselor = row<SqlRow>('SELECT email, name, department, year_level FROM users WHERE email = ? LIMIT 1', [
    String(counselorEmail || '').trim().toLowerCase(),
  ]);
  if (!counselor) return [];
  const actor = toAuthUser(counselor);
  const all = getNoticeRecordsForActor(actor, options);
  const normalizedEmail = String(counselorEmail || '').trim().toLowerCase();
  const counselorStudentCount = Number(
    row<{ count: number }>(
      'SELECT COUNT(*) AS count FROM counselor_students WHERE LOWER(TRIM(counselor_email)) = LOWER(TRIM(?)) AND COALESCE(is_active, 1) = 1',
      [normalizedEmail],
    )?.count || 0,
  );
  return all.map((item) => {
    const sentCount = Math.min(
      counselorStudentCount,
      Number(
        row<{ count: number }>(
          'SELECT COUNT(*) AS count FROM notice_deliveries WHERE notice_id = ? AND LOWER(TRIM(counselor_email)) = LOWER(TRIM(?))',
          [item.id, normalizedEmail],
        )?.count || 0,
      ),
    );
    const isComplete = counselorStudentCount > 0 && sentCount >= counselorStudentCount;
    return {
      ...item,
      student_count: counselorStudentCount,
      sent_students: sentCount,
      total_students: counselorStudentCount,
      completion_status: isComplete ? 'completed' : 'pending',
      completed_counselors: isComplete ? 1 : 0,
      total_counselors: 1,
    };
  });
}

export function canCounselorAccessNotice(noticeId: number, counselorEmail: string) {
  const counselor = row<SqlRow>('SELECT department, year_level FROM users WHERE email = ? LIMIT 1', [
    String(counselorEmail || '').trim().toLowerCase(),
  ]);
  if (!counselor) return false;

  const notice = getNotice(noticeId);
  if (!notice) return false;
  if (Boolean(Number(notice.send_to_all || 0))) return true;

  const department = String(counselor.department || '').trim().toUpperCase();
  const yearLevel = Number(counselor.year_level || 1);
  return getNoticeScopePairs(noticeId).some((scope) => scope.department === department && scope.year_level === yearLevel);
}

export function getNoticeSentRegNos(counselorEmail: string, noticeId: number) {
  return new Set(
    rows<{ reg_no: string }>(
      `
        SELECT DISTINCT reg_no
        FROM notice_deliveries
        WHERE counselor_email = ?
          AND notice_id = ?
          AND LOWER(COALESCE(status, 'sent')) = 'sent'
      `,
      [String(counselorEmail || '').trim().toLowerCase(), noticeId],
    ).map((item) => String(item.reg_no || '').trim().toUpperCase()),
  );
}

export function getCounselorSendNoticeRows(noticeId: number, counselorEmail: string) {
  const notice = getNotice(noticeId) || {};
  const user = getUserByEmail(counselorEmail) || null;
  const students = getStudentsForCounselor(counselorEmail);
  const sentRegNos = getNoticeSentRegNos(counselorEmail, noticeId);

  return students
    .map((student) => {
      const regNo = String(student.reg_no || '').trim().toUpperCase();
      if (!regNo) return null;
      return {
        reg_no: regNo,
        student_name: student.student_name || regNo,
        parent_phone: student.parent_phone || '',
        department: student.department || String(notice.department || user?.department || ''),
        status: sentRegNos.has(regNo) ? 'Generated' : 'Pending',
      } satisfies CounselorSendNoticeRow;
    })
    .filter((item): item is CounselorSendNoticeRow => !!item);
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

export interface CounselorStudentRecord {
  reg_no: string;
  student_name: string;
  department: string;
  parent_phone: string;
  parent_email: string;
}

export function saveCounselorStudent(
  counselorEmail: string,
  payload: { reg_no: string; student_name: string; department?: string; parent_phone?: string; parent_email?: string },
) {
  const email = String(counselorEmail || '').trim().toLowerCase();
  const regNo = String(payload.reg_no || '').trim();
  const studentName = String(payload.student_name || '').trim();
  const department = String(payload.department || '').trim().toUpperCase();
  const parentPhone = String(payload.parent_phone || '').trim();
  const parentEmail = String(payload.parent_email || '').trim();
  if (!email || !regNo || !studentName) {
    throw new Error('Counselor, reg no, and student name are required.');
  }

  const existing = row<{ count: number }>(
    'SELECT COUNT(*) AS count FROM counselor_students WHERE counselor_email = ? AND reg_no = ?',
    [email, regNo],
  );

  if (Number(existing?.count || 0) > 0) {
    db.prepare(`
      UPDATE counselor_students
      SET student_name = ?, department = ?, parent_phone = ?, parent_email = ?, is_active = 1
      WHERE counselor_email = ? AND reg_no = ?
    `).run(studentName, department, parentPhone, parentEmail, email, regNo);
  } else {
    db.prepare(`
      INSERT INTO counselor_students (counselor_email, reg_no, student_name, department, parent_phone, parent_email, is_active)
      VALUES (?, ?, ?, ?, ?, ?, 1)
    `).run(email, regNo, studentName, department, parentPhone, parentEmail);
  }
}

export function addStudentsBulk(
  counselorEmail: string,
  students: Array<{ reg_no: string; student_name: string; department?: string; parent_phone?: string; parent_email?: string }>,
) {
  const transaction = db.transaction((rowsToSave: Array<{ reg_no: string; student_name: string; department?: string; parent_phone?: string; parent_email?: string }>) => {
    let count = 0;
    for (const student of rowsToSave || []) {
      if (!String(student.reg_no || '').trim() || !String(student.student_name || '').trim()) continue;
      saveCounselorStudent(counselorEmail, student);
      count += 1;
    }
    return count;
  });
  return transaction(students || []);
}

export function deleteCounselorStudent(counselorEmail: string, regNo: string) {
  return db.prepare('DELETE FROM counselor_students WHERE counselor_email = ? AND reg_no = ?').run(
    String(counselorEmail || '').trim().toLowerCase(),
    String(regNo || '').trim(),
  );
}

export function deleteAllCounselorStudents(counselorEmail: string) {
  return db.prepare('DELETE FROM counselor_students WHERE counselor_email = ?').run(String(counselorEmail || '').trim().toLowerCase());
}

export interface CounselorSendReportRow {
  reg_no: string;
  student_name: string;
  parent_phone: string;
  department: string;
  marks: Record<string, string>;
  status: 'Generated' | 'Pending';
}

export interface CounselorSendNoticeRow {
  reg_no: string;
  student_name: string;
  parent_phone: string;
  department: string;
  status: 'Generated' | 'Pending';
}

export interface ExistingScopedTestRecord {
  test_id: number;
  file_hash: string;
  uploaded_by: string;
  uploaded_at: string;
}

export function getAllUniqueTests(options?: {
  filterDept?: string | null;
  filterYearLevel?: number | null;
  allowedScopes?: Set<string> | null;
}) {
  const filterDept = String(options?.filterDept || '').trim().toUpperCase();
  const filterYearLevel = Number(options?.filterYearLevel || 0) || null;
  const allowedScopes = options?.allowedScopes || null;

  const allRows = rows<SqlRow>(`
    SELECT
      t.id,
      t.test_name AS t_name,
      tm.id AS tm_id,
      tm.test_id,
      tm.test_name,
      tm.batch_name,
      tm.semester,
      COALESCE(
        NULLIF(tm.department, ''),
        (
          SELECT sm.department
          FROM student_marks sm
          WHERE sm.test_id = t.id
            AND TRIM(COALESCE(sm.department, '')) <> ''
          LIMIT 1
        ),
        (
          SELECT u2.department
          FROM users u2
          WHERE u2.email = tm.uploaded_by
          LIMIT 1
        ),
        ''
      ) AS department,
      tm.section,
      tm.year_level,
      tm.uploaded_at,
      tm.uploaded_by,
      COALESCE(tm.is_blocked, 0) AS is_blocked,
      u.name AS uploaded_by_name,
      (
        SELECT COUNT(DISTINCT sm.reg_no)
        FROM student_marks sm
        WHERE sm.test_id = t.id
      ) AS student_count
    FROM tests t
    LEFT JOIN test_metadata tm ON tm.test_id = t.id
    LEFT JOIN users u ON tm.uploaded_by = u.email
    ORDER BY COALESCE(tm.uploaded_at, t.test_date) DESC, t.id DESC
  `);

  const seen = new Set<string>();
  const result: ReportTestRecord[] = [];

  for (const item of allRows) {
    const department = String(item.department || '').trim().toUpperCase();
    const yearLevel = Number(item.year_level || 0) || 1;
    const semester = String(item.semester || '').trim();
    const section = String(item.section || '').trim();
    const testName = String(item.test_name || item.t_name || `Test #${item.id}`).trim();
    const batchName = String(item.batch_name || '').trim();
    const scopeKey = `${department}::${yearLevel}`;

    if (filterDept && department !== filterDept) continue;
    if (filterYearLevel && yearLevel !== filterYearLevel) continue;
    if (allowedScopes && !allowedScopes.has(scopeKey)) continue;

    const uniqueKey = [
      testName.toLowerCase(),
      batchName.toLowerCase(),
      semester.toLowerCase(),
      department.toLowerCase(),
      String(yearLevel),
      section.toLowerCase(),
    ].join('|');
    const dedupeKey = uniqueKey.replace(/\|/g, '') ? uniqueKey : `id:${item.id}`;
    if (seen.has(dedupeKey)) continue;
    seen.add(dedupeKey);

    result.push({
      id: Number(item.id || 0),
      test_id: Number(item.test_id || item.id || 0),
      test_name: testName,
      batch_name: batchName,
      semester,
      department,
      year_level: yearLevel,
      section,
      uploaded_at: String(item.uploaded_at || ''),
      uploaded_by: String(item.uploaded_by || ''),
      uploaded_by_name: String(item.uploaded_by_name || item.uploaded_by || ''),
      student_count: Number(item.student_count || 0),
      is_blocked: Number(item.is_blocked || 0),
    });
  }

  return result.sort((a, b) => {
    const nameCompare = a.test_name.localeCompare(b.test_name);
    if (nameCompare !== 0) return nameCompare;
    return String(b.uploaded_at || '').localeCompare(String(a.uploaded_at || ''));
  });
}

export function getStudentCountForCounselor(counselorEmail: string) {
  return Number(
    (
      row<{ count: number }>('SELECT COUNT(*) AS count FROM counselor_students WHERE counselor_email = ?', [counselorEmail])
        ?.count || 0
    ),
  );
}

export function getStudentsForCounselor(counselorEmail: string) {
  return rows<SqlRow>(
    'SELECT reg_no, student_name, department, parent_phone, parent_email FROM counselor_students WHERE counselor_email = ? ORDER BY student_name',
    [counselorEmail],
  ).map((item) => ({
    reg_no: String(item.reg_no || ''),
    student_name: String(item.student_name || item.reg_no || ''),
    department: String(item.department || ''),
    parent_phone: String(item.parent_phone || ''),
    parent_email: String(item.parent_email || ''),
  } satisfies CounselorStudentRecord));
}

export function getVisibleTestsForCounselor(counselorEmail: string) {
  return rows<SqlRow>(
    `
      SELECT DISTINCT
        t.id,
        COALESCE(tm.test_name, t.test_name) AS test_name,
        COALESCE(tm.semester, '') AS semester,
        COALESCE(
          NULLIF(tm.department, ''),
          (
            SELECT sm.department
            FROM student_marks sm
            WHERE sm.test_id = t.id
              AND TRIM(COALESCE(sm.department, '')) <> ''
            LIMIT 1
          ),
          COALESCE(u.department, '')
        ) AS department,
        COALESCE(tm.year_level, 1) AS year_level,
        COALESCE(tm.batch_name, '') AS batch_name,
        COALESCE(tm.section, '') AS section,
        COALESCE(tm.is_blocked, 0) AS is_blocked,
        tm.uploaded_at,
        tm.uploaded_by,
        (
          SELECT u2.name
          FROM users u2
          WHERE u2.email = tm.uploaded_by
          LIMIT 1
        ) AS uploaded_by_name,
        (
          SELECT COUNT(DISTINCT sm.reg_no)
          FROM student_marks sm
          JOIN counselor_students cs
            ON REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
          WHERE sm.test_id = t.id
            AND LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(?))
            AND COALESCE(cs.is_active, 1) = 1
        ) AS student_count,
        (
          SELECT COUNT(DISTINCT s2.reg_no)
          FROM sent_messages s2
          WHERE s2.test_id = t.id AND s2.counselor_email = ?
        ) AS generated_count
      FROM tests t
      JOIN test_metadata tm ON t.id = tm.test_id
      JOIN users u ON u.email = ?
      WHERE COALESCE(
              NULLIF(tm.department, ''),
              (
                SELECT sm.department
                FROM student_marks sm
                WHERE sm.test_id = t.id
                  AND TRIM(COALESCE(sm.department, '')) <> ''
                LIMIT 1
              ),
              COALESCE(u.department, '')
            ) = COALESCE(u.department, '')
        AND COALESCE(tm.year_level, 1) = COALESCE(u.year_level, 1)
        AND EXISTS (
          SELECT 1
          FROM student_marks sm
          JOIN counselor_students cs
            ON REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
          WHERE sm.test_id = t.id
            AND LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(?))
            AND COALESCE(cs.is_active, 1) = 1
        )
      ORDER BY tm.uploaded_at DESC, t.id DESC
    `,
    [counselorEmail, counselorEmail, counselorEmail, counselorEmail],
  ).map((item) => ({
    id: Number(item.id || 0),
    test_id: Number(item.id || 0),
    test_name: String(item.test_name || `Test #${item.id || 0}`),
    batch_name: String(item.batch_name || ''),
    semester: String(item.semester || ''),
    department: String(item.department || '').trim().toUpperCase(),
    year_level: Number(item.year_level || 1),
    section: String(item.section || ''),
    uploaded_at: String(item.uploaded_at || ''),
    uploaded_by: String(item.uploaded_by || ''),
    uploaded_by_name: String(item.uploaded_by_name || item.uploaded_by || ''),
    student_count: Number(item.student_count || 0),
    generated_count: Number(item.generated_count || 0),
    is_blocked: Number(item.is_blocked || 0),
  } satisfies CounselorVisibleTestRecord));
}

export function getVisibleTestCountForCounselor(counselorEmail: string) {
  return Number(
    (
      row<{ count: number }>(
        `
          SELECT COUNT(DISTINCT t.id) AS count
          FROM tests t
          JOIN test_metadata tm ON t.id = tm.test_id
          JOIN users u ON u.email = ?
          WHERE COALESCE(
                  NULLIF(tm.department, ''),
                  (
                    SELECT sm.department
                    FROM student_marks sm
                    WHERE sm.test_id = t.id
                      AND TRIM(COALESCE(sm.department, '')) <> ''
                    LIMIT 1
                  ),
                  COALESCE(u.department, '')
                ) = COALESCE(u.department, '')
            AND COALESCE(tm.year_level, 1) = COALESCE(u.year_level, 1)
            AND EXISTS (
              SELECT 1
              FROM student_marks sm
              JOIN counselor_students cs
                ON REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
              WHERE sm.test_id = t.id
                AND LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(?))
                AND COALESCE(cs.is_active, 1) = 1
            )
        `,
        [counselorEmail, counselorEmail],
      )?.count || 0
    ),
  );
}

export function canCounselorAccessTest(testId: number, counselorEmail: string) {
  const found = row<{ id: number }>(
    `
      SELECT t.id
      FROM tests t
      JOIN test_metadata tm ON t.id = tm.test_id
      JOIN users u ON u.email = ?
      WHERE t.id = ?
        AND COALESCE(
              NULLIF(tm.department, ''),
              (
                SELECT sm.department
                FROM student_marks sm
                WHERE sm.test_id = t.id
                  AND TRIM(COALESCE(sm.department, '')) <> ''
                LIMIT 1
              ),
              COALESCE(u.department, '')
            ) = COALESCE(u.department, '')
        AND COALESCE(tm.year_level, 1) = COALESCE(u.year_level, 1)
        AND EXISTS (
          SELECT 1
          FROM student_marks sm
          JOIN counselor_students cs
            ON REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
          WHERE sm.test_id = t.id
            AND LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(?))
            AND COALESCE(cs.is_active, 1) = 1
        )
      LIMIT 1
    `,
    [counselorEmail, testId, counselorEmail],
  );
  return !!found;
}

export function canCounselorAccessStudent(testId: number, counselorEmail: string, regNo: string) {
  const normalizedEmail = String(counselorEmail || '').trim().toLowerCase();
  const normalizedRegNo = String(regNo || '').trim();
  if (!normalizedEmail || !normalizedRegNo) return false;
  const found = row<{ reg_no: string }>(
    `
      SELECT cs.reg_no
      FROM counselor_students cs
      JOIN student_marks sm
        ON REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '')
      WHERE sm.test_id = ?
        AND LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(?))
        AND REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(?)), '.0', '')
        AND COALESCE(cs.is_active, 1) = 1
      LIMIT 1
    `,
    [testId, normalizedEmail, normalizedRegNo],
  );
  return !!found;
}

export function getTestMarksGroupedForCounselor(testId: number, counselorEmail: string) {
  const grouped = getTestMarksGrouped(testId);
  const allowedRegNos = new Set(
    rows<{ reg_no: string }>('SELECT reg_no FROM counselor_students WHERE counselor_email = ?', [counselorEmail]).map((item) =>
      String(item.reg_no || '').trim(),
    ),
  );

  const overrides = rows<{ reg_no: string; subject_name: string; marks: string }>(
    `
      SELECT reg_no, subject_name, marks
      FROM counselor_mark_overrides
      WHERE counselor_email = ? AND test_id = ?
    `,
    [counselorEmail, testId],
  );

  const students = grouped.students
    .filter((student) => allowedRegNos.has(String(student.reg_no || '').trim()))
    .map((student) => ({
      ...student,
      marks: { ...student.marks },
    }));

  const studentsByReg = new Map(students.map((student) => [String(student.reg_no || '').trim(), student]));
  for (const override of overrides) {
    const regNo = String(override.reg_no || '').trim();
    const subjectName = String(override.subject_name || '').trim();
    if (!studentsByReg.has(regNo) || !subjectName || isAttendanceField(subjectName)) continue;
    studentsByReg.get(regNo)!.marks[subjectName] = String(override.marks || '');
  }

  return {
    subjects: grouped.subjects,
    students,
  };
}

export function getCounselorMessageStats(counselorEmail: string): CounselorMessageStats {
  return {
    total: Number((row<{ count: number }>('SELECT COUNT(*) AS count FROM sent_messages WHERE counselor_email = ?', [counselorEmail])?.count || 0)),
    today: Number(
      (
        row<{ count: number }>(
          "SELECT COUNT(*) AS count FROM sent_messages WHERE counselor_email = ? AND DATE(sent_at) = DATE('now')",
          [counselorEmail],
        )?.count || 0
      ),
    ),
    week: Number(
      (
        row<{ count: number }>(
          "SELECT COUNT(*) AS count FROM sent_messages WHERE counselor_email = ? AND sent_at >= DATE('now','-7 days')",
          [counselorEmail],
        )?.count || 0
      ),
    ),
    month: Number(
      (
        row<{ count: number }>(
          "SELECT COUNT(*) AS count FROM sent_messages WHERE counselor_email = ? AND sent_at >= DATE('now','-30 days')",
          [counselorEmail],
        )?.count || 0
      ),
    ),
    unique: Number(
      (
        row<{ count: number }>('SELECT COUNT(DISTINCT reg_no) AS count FROM sent_messages WHERE counselor_email = ?', [counselorEmail])?.count || 0
      ),
    ),
  };
}

export function getCounselorMessageHistory(counselorEmail: string, limit = 50) {
  return rows<SqlRow>(
    `
      SELECT sm.*, u.name AS counselor_name
      FROM sent_messages sm
      LEFT JOIN users u ON sm.counselor_email = u.email
      WHERE sm.counselor_email = ?
      ORDER BY sm.sent_at DESC
      LIMIT ?
    `,
    [counselorEmail, limit],
  ).map((item) => ({
    id: Number(item.id || 0),
    reg_no: String(item.reg_no || ''),
    student_name: String(item.student_name || ''),
    counselor_email: String(item.counselor_email || ''),
    counselor_name: String(item.counselor_name || item.counselor_email || ''),
    message_type: String(item.message_type || item.format || ''),
    status: String(item.status || ''),
    whatsapp_link: String(item.whatsapp_link || ''),
    sent_at: String(item.sent_at || ''),
    test_id: item.test_id === null || item.test_id === undefined ? null : Number(item.test_id || 0),
    send_mode: String(item.send_mode || 'app'),
  } satisfies CounselorMessageRecord));
}

export function getMessageHistoryFiltered(options?: {
  day?: string | null;
  counselorQuery?: string | null;
  limit?: number | null;
  filterYear?: string | null;
  filterMonth?: string | null;
  filterDay?: string | null;
  allowedCounselors?: string[] | null;
}) {
  const where: string[] = [];
  const params: unknown[] = [];

  if (options?.day) {
    where.push('DATE(sm.sent_at) = ?');
    params.push(String(options.day));
  } else {
    if (options?.filterYear) {
      where.push("strftime('%Y', sm.sent_at) = ?");
      params.push(String(options.filterYear).padStart(4, '0'));
    }
    if (options?.filterMonth) {
      where.push("strftime('%m', sm.sent_at) = ?");
      params.push(String(options.filterMonth).padStart(2, '0'));
    }
    if (options?.filterDay) {
      where.push("strftime('%d', sm.sent_at) = ?");
      params.push(String(options.filterDay).padStart(2, '0'));
    }
  }

  if (options?.counselorQuery) {
    const q = `%${String(options.counselorQuery).trim().toLowerCase()}%`;
    where.push("(LOWER(COALESCE(u.name, '')) LIKE ? OR LOWER(COALESCE(sm.counselor_email, '')) LIKE ?)");
    params.push(q, q);
  }

  if (options?.allowedCounselors) {
    const allowed = options.allowedCounselors.map((item) => String(item || '').trim().toLowerCase()).filter(Boolean);
    if (!allowed.length) return [];
    where.push(`LOWER(COALESCE(sm.counselor_email, '')) IN (${allowed.map(() => '?').join(',')})`);
    params.push(...allowed);
  }

  const limitSql = options?.limit === null ? '' : 'LIMIT ?';
  if (options?.limit !== null) {
    params.push(Number(options?.limit || 500));
  }

  const whereSql = where.length ? `WHERE ${where.join(' AND ')}` : '';
  return rows<SqlRow>(
    `
      SELECT sm.*, u.name AS counselor_name
      FROM sent_messages sm
      LEFT JOIN users u ON sm.counselor_email = u.email
      ${whereSql}
      ORDER BY sm.sent_at DESC
      ${limitSql}
    `,
    params,
  ).map((item) => ({
    id: Number(item.id || 0),
    reg_no: String(item.reg_no || ''),
    student_name: String(item.student_name || ''),
    counselor_email: String(item.counselor_email || ''),
    counselor_name: String(item.counselor_name || item.counselor_email || ''),
    message_type: String(item.message_type || item.format || ''),
    status: String(item.status || ''),
    whatsapp_link: String(item.whatsapp_link || ''),
    sent_at: String(item.sent_at || ''),
    test_id: item.test_id === null || item.test_id === undefined ? null : Number(item.test_id || 0),
    send_mode: String(item.send_mode || 'app'),
  } satisfies AdminMessageRecord));
}

export function getMessageDays(counselorQuery?: string | null, allowedCounselors?: string[] | null) {
  const where: string[] = [];
  const params: unknown[] = [];
  if (counselorQuery) {
    const q = `%${String(counselorQuery).trim().toLowerCase()}%`;
    where.push("(LOWER(COALESCE(u.name, '')) LIKE ? OR LOWER(COALESCE(sm.counselor_email, '')) LIKE ?)");
    params.push(q, q);
  }
  if (allowedCounselors) {
    const allowed = allowedCounselors.map((item) => String(item || '').trim().toLowerCase()).filter(Boolean);
    if (!allowed.length) return [];
    where.push(`LOWER(COALESCE(sm.counselor_email, '')) IN (${allowed.map(() => '?').join(',')})`);
    params.push(...allowed);
  }
  const whereSql = where.length ? `WHERE ${where.join(' AND ')}` : '';
  return rows<SqlRow>(
    `
      SELECT COALESCE(DATE(sm.sent_at), 'Unknown') AS day,
             COUNT(*) AS total,
             COUNT(DISTINCT sm.counselor_email) AS counselors
      FROM sent_messages sm
      LEFT JOIN users u ON sm.counselor_email = u.email
      ${whereSql}
      GROUP BY DATE(sm.sent_at)
      ORDER BY day DESC
    `,
    params,
  ).map((item) => ({
    day: String(item.day || 'Unknown'),
    total: Number(item.total || 0),
    counselors: Number(item.counselors || 0),
  } satisfies MessageDayRecord));
}

export function getMessageCounselorSuggestions(query = '', allowedCounselors?: string[] | null, limit = 25) {
  const where = ["LOWER(COALESCE(u.role, '')) IN ('counselor','deo')"];
  const params: unknown[] = [];
  const trimmed = String(query || '').trim().toLowerCase();
  if (trimmed) {
    const likeQ = `%${trimmed}%`;
    where.push("(LOWER(COALESCE(u.name, '')) LIKE ? OR LOWER(COALESCE(u.email, '')) LIKE ?)");
    params.push(likeQ, likeQ);
  }
  if (allowedCounselors) {
    const allowed = allowedCounselors.map((item) => String(item || '').trim().toLowerCase()).filter(Boolean);
    if (!allowed.length) return [];
    where.push(`LOWER(u.email) IN (${allowed.map(() => '?').join(',')})`);
    params.push(...allowed);
  }
  params.push(limit);
  return rows<SqlRow>(
    `
      SELECT DISTINCT u.name, u.email
      FROM users u
      WHERE ${where.join(' AND ')}
      ORDER BY u.name
      LIMIT ?
    `,
    params,
  ).map((item) => ({
    name: String(item.name || ''),
    email: String(item.email || ''),
  } satisfies MessageCounselorSuggestion));
}

export function deleteMessageById(messageId: number) {
  const info = db.prepare('DELETE FROM sent_messages WHERE id = ?').run(Number(messageId || 0));
  return Number(info.changes || 0);
}

export function deleteMessagesByIds(messageIds: number[]) {
  const ids = messageIds.map((item) => Number(item || 0)).filter((item) => item > 0);
  if (!ids.length) return 0;
  const info = db.prepare(`DELETE FROM sent_messages WHERE id IN (${ids.map(() => '?').join(',')})`).run(...ids);
  return Number(info.changes || 0);
}

export function getAdminMessageStats() {
  return {
    total: Number(row<{ count: number }>('SELECT COUNT(*) AS count FROM sent_messages')?.count || 0),
    today: Number(row<{ count: number }>("SELECT COUNT(*) AS count FROM sent_messages WHERE DATE(sent_at) = DATE('now')")?.count || 0),
    active_counselors: Number(row<{ count: number }>('SELECT COUNT(DISTINCT counselor_email) AS count FROM sent_messages')?.count || 0),
  };
}

export function getSentRegNosForTest(counselorEmail: string, testId: number) {
  return new Set(
    rows<{ reg_no: string }>(
      "SELECT DISTINCT reg_no FROM sent_messages WHERE counselor_email = ? AND test_id = ? AND LOWER(COALESCE(status, 'sent')) = 'sent'",
      [counselorEmail, testId],
    ).map((item) => String(item.reg_no || '').trim().toUpperCase()),
  );
}

export function getStudentMarksForReg(testId: number, regNo: string) {
  const result: Record<string, string> = {};
  const rowsForStudent = rows<{ subject_name: string; marks: string }>(
    'SELECT subject_name, marks FROM student_marks WHERE test_id = ? AND reg_no = ?',
    [testId, regNo],
  );
  for (const item of rowsForStudent) {
    const subjectName = String(item.subject_name || '').trim();
    if (!subjectName) continue;
    result[subjectName] = String(item.marks ?? '');
  }
  return result;
}

export function getStudentMarksForRegForCounselor(testId: number, regNo: string, counselorEmail: string) {
  const merged = { ...getStudentMarksForReg(testId, regNo) };
  const overrides = rows<{ subject_name: string; marks: string }>(
    `
      SELECT subject_name, marks
      FROM counselor_mark_overrides
      WHERE counselor_email = ? AND test_id = ? AND reg_no = ?
    `,
    [counselorEmail, testId, regNo],
  );

  for (const item of overrides) {
    const subjectName = String(item.subject_name || '').trim();
    if (!subjectName) continue;
    merged[subjectName] = String(item.marks ?? '');
  }
  return merged;
}

export function getCounselorSendReportRows(testId: number, counselorEmail: string) {
  const testMeta = getTestMetadata(testId) || {};
  const user = getUserByEmail(counselorEmail) || null;
  const students = getStudentsForCounselor(counselorEmail);
  const byReg = new Map(
    students.map((student) => [String(student.reg_no || '').trim().toUpperCase(), student]),
  );
  const grouped = getTestMarksGroupedForCounselor(testId, counselorEmail);
  const sentRegNos = getSentRegNosForTest(counselorEmail, testId);

  const rowsForSend: CounselorSendReportRow[] = [];
  for (const student of grouped.students || []) {
    const regNo = String(student.reg_no || '').trim().toUpperCase();
    if (!regNo || !byReg.has(regNo)) continue;
    const mappedStudent = byReg.get(regNo)!;
    rowsForSend.push({
      reg_no: regNo,
      student_name: mappedStudent.student_name || student.student_name || regNo,
      parent_phone: mappedStudent.parent_phone || '',
      department: mappedStudent.department || String(testMeta.department || user?.department || ''),
      marks: student.marks || {},
      status: sentRegNos.has(regNo) ? 'Generated' : 'Pending',
    });
  }

  return rowsForSend;
}

export function getCounselorActivityScopeSnapshot(
  department: string,
  yearLevel: number,
  tests?: Array<Pick<ReportTestRecord, 'test_id' | 'department' | 'year_level' | 'semester' | 'test_name'>>,
) {
  const toPercentInt = (completed: number, total: number) => {
    const safeCompleted = Math.max(0, Number(completed || 0));
    const safeTotal = Math.max(0, Number(total || 0));
    if (safeTotal <= 0) return 100;
    if (safeCompleted >= safeTotal) return 100;
    return Math.max(0, Math.floor((safeCompleted / safeTotal) * 100));
  };

  const dep = String(department || '').trim().toUpperCase();
  const yr = Math.max(1, Number(yearLevel || 1) || 1);
  const scopeTests = (tests || getAllUniqueTests({ filterDept: dep, filterYearLevel: yr }))
    .map((item) => ({
      test_id: Number(item.test_id || 0) || 0,
      department: String(item.department || dep).trim().toUpperCase(),
      year_level: Number(item.year_level || yr) || yr,
      semester: String(item.semester || '').trim(),
      test_name: String(item.test_name || '').trim().toUpperCase(),
    }))
    .filter((item) => item.department === dep && item.year_level === yr && ['1', '2'].includes(item.semester) && ['IAT 1', 'IAT 2', 'MODEL EXAM'].includes(item.test_name));

  const testStatus: Record<string, Record<string, boolean>> = {
    '1': { 'IAT 1': false, 'IAT 2': false, 'MODEL EXAM': false },
    '2': { 'IAT 1': false, 'IAT 2': false, 'MODEL EXAM': false },
  };
  const testsByKey = new Map<string, { test_id: number; semester: string; test_name: string }>();
  for (const test of scopeTests) {
    const key = `${test.semester}::${test.test_name}`;
    if (!testsByKey.has(key)) testsByKey.set(key, { test_id: test.test_id, semester: test.semester, test_name: test.test_name });
    if (testStatus[test.semester] && Object.prototype.hasOwnProperty.call(testStatus[test.semester], test.test_name)) {
      testStatus[test.semester][test.test_name] = true;
    }
  }

  const counselors = rows<SqlRow>(
    `
      SELECT email, name, department, year_level, last_login
      FROM users
      WHERE LOWER(COALESCE(role, '')) = 'counselor'
        AND UPPER(COALESCE(department, '')) = ?
        AND COALESCE(year_level, 1) = ?
      ORDER BY name ASC
    `,
    [dep, yr],
  );

  const eligibleCounts = new Map<string, number>();
  const eligiblePhoneCounts = new Map<string, number>();
  const sentCounts = new Map<string, number>();
  const testIds = Array.from(new Set(Array.from(testsByKey.values()).map((item) => Number(item.test_id || 0)).filter((value) => value > 0)));
  if (testIds.length) {
    const placeholders = testIds.map(() => '?').join(', ');
    for (const item of rows<{ counselor_email: string; test_id: number; count: number }>(
      `
        SELECT LOWER(TRIM(cs.counselor_email)) AS counselor_email,
               sm.test_id AS test_id,
               COUNT(DISTINCT REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '')) AS count
        FROM counselor_students cs
        INNER JOIN student_marks sm
          ON REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
        WHERE COALESCE(cs.is_active, 1) = 1
          AND sm.test_id IN (${placeholders})
        GROUP BY LOWER(TRIM(cs.counselor_email)), sm.test_id
      `,
      testIds,
    )) {
      eligibleCounts.set(`${String(item.counselor_email || '').trim().toLowerCase()}::${Number(item.test_id || 0)}`, Number(item.count || 0));
    }

    for (const item of rows<{ counselor_email: string; test_id: number; count: number }>(
      `
        SELECT LOWER(TRIM(cs.counselor_email)) AS counselor_email,
               sm.test_id AS test_id,
               COUNT(DISTINCT REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '')) AS count
        FROM counselor_students cs
        INNER JOIN student_marks sm
          ON REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
        WHERE COALESCE(cs.is_active, 1) = 1
          AND COALESCE(TRIM(cs.parent_phone), '') <> ''
          AND sm.test_id IN (${placeholders})
        GROUP BY LOWER(TRIM(cs.counselor_email)), sm.test_id
      `,
      testIds,
    )) {
      eligiblePhoneCounts.set(`${String(item.counselor_email || '').trim().toLowerCase()}::${Number(item.test_id || 0)}`, Number(item.count || 0));
    }

    for (const item of rows<{ counselor_email: string; test_id: number; count: number }>(
      `
        SELECT LOWER(TRIM(m.counselor_email)) AS counselor_email,
               m.test_id AS test_id,
               COUNT(DISTINCT REPLACE(UPPER(TRIM(m.reg_no)), '.0', '')) AS count
        FROM sent_messages m
        INNER JOIN counselor_students cs
          ON LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(m.counselor_email))
         AND COALESCE(cs.is_active, 1) = 1
         AND REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(m.reg_no)), '.0', '')
        WHERE m.test_id IN (${placeholders})
        GROUP BY LOWER(TRIM(m.counselor_email)), m.test_id
      `,
      testIds,
    )) {
      sentCounts.set(`${String(item.counselor_email || '').trim().toLowerCase()}::${Number(item.test_id || 0)}`, Number(item.count || 0));
    }
  }

  const results = Array.from(testsByKey.values()).map((test) => {
    const rowsForTest = counselors.map((item) => {
      const email = String(item.email || '').trim().toLowerCase();
      const compositeKey = `${email}::${Number(test.test_id || 0)}`;
      const studentCount = eligibleCounts.get(compositeKey) || 0;
      const withPhone = eligiblePhoneCounts.get(compositeKey) || 0;
      const sentCount = sentCounts.get(compositeKey) || 0;
      const boundedSentCount = Math.min(sentCount, studentCount);
      const completionPct = toPercentInt(boundedSentCount, studentCount);
      const pendingCount = Math.max(0, studentCount - boundedSentCount);
      const workStatus: CounselorActivityRow['work_status'] = pendingCount === 0 ? 'Complete' : 'Pending';
      return {
        email,
        name: String(item.name || email),
        department: String(item.department || dep),
        year_level: Number(item.year_level || yr),
        last_login: String(item.last_login || ''),
        student_count: studentCount,
        students_with_phone: withPhone,
        total_messages: boundedSentCount,
        unique_students_messaged: boundedSentCount,
        pending_count: pendingCount,
        completion_pct: completionPct,
        work_status: workStatus,
        tests_uploaded: Number(test.test_id || 0) ? 1 : 0,
        week_messages: 0,
      } satisfies CounselorActivityRow;
    });

    return {
      test_id: Number(test.test_id || 0) || null,
      department: dep,
      year_level: yr,
      semester: test.semester,
      test_name: test.test_name,
      rows: rowsForTest.sort((a, b) => {
        const statusCompare = (a.work_status === 'Complete' ? 1 : 0) - (b.work_status === 'Complete' ? 1 : 0);
        if (statusCompare !== 0) return statusCompare;
        if (b.pending_count !== a.pending_count) return b.pending_count - a.pending_count;
        return a.name.localeCompare(b.name);
      }),
      stats: {
        total_counselors: rowsForTest.length,
        complete: rowsForTest.filter((item) => item.work_status === 'Complete').length,
        pending: rowsForTest.filter((item) => item.work_status !== 'Complete').length,
        avg_completion: rowsForTest.length ? Math.round(rowsForTest.reduce((sum, item) => sum + item.completion_pct, 0) / rowsForTest.length) : 0,
      },
    } satisfies CounselorActivityResult;
  });

  return {
    department: dep,
    year_level: yr,
    test_status: testStatus,
    results,
  } satisfies CounselorActivityScopeSnapshot;
}

export function getCounselorActivityForTest(
  department: string,
  yearLevel: number,
  semester: string,
  testName: string,
  searchQuery = '',
  sortMode = 'pending_first',
) {
  const dep = String(department || '').trim().toUpperCase();
  const yr = Math.max(1, Number(yearLevel || 1) || 1);
  const normalizedSemester = String(semester || '').trim();
  const normalizedTestName = String(testName || '').trim().toUpperCase();
  const snapshot = getCounselorActivityScopeSnapshot(dep, yr);
  const matched = snapshot.results.find((item) => item.semester === normalizedSemester && item.test_name === normalizedTestName);
  if (!matched) {
    return {
      test_id: null,
      department: dep,
      year_level: yr,
      semester: normalizedSemester,
      test_name: normalizedTestName,
      rows: [],
      stats: {
        total_counselors: 0,
        complete: 0,
        pending: 0,
        avg_completion: 0,
      },
    } satisfies CounselorActivityResult;
  }

  let result = matched.rows;
  const query = String(searchQuery || '').trim().toLowerCase();
  if (query) {
    result = result.filter((item) => item.name.toLowerCase().includes(query) || item.email.toLowerCase().includes(query));
  }

  if (sortMode === 'name_desc') {
    result = [...result].sort((a, b) => b.name.localeCompare(a.name));
  } else if (sortMode === 'name_asc') {
    result = [...result].sort((a, b) => a.name.localeCompare(b.name));
  } else {
    result = [...result].sort((a, b) => {
      const statusCompare = (a.work_status === 'Complete' ? 1 : 0) - (b.work_status === 'Complete' ? 1 : 0);
      if (statusCompare !== 0) return statusCompare;
      if (b.pending_count !== a.pending_count) return b.pending_count - a.pending_count;
      return a.name.localeCompare(b.name);
    });
  }

  return {
    ...matched,
    rows: result,
    stats: {
      total_counselors: result.length,
      complete: result.filter((item) => item.work_status === 'Complete').length,
      pending: result.filter((item) => item.work_status !== 'Complete').length,
      avg_completion: result.length ? Math.round(result.reduce((sum, item) => sum + item.completion_pct, 0) / result.length) : 0,
    },
  } satisfies CounselorActivityResult;
}

export function getCounselorActivitySummary() {
  const toPercentInt = (completed: number, total: number) => {
    const safeCompleted = Math.max(0, Number(completed || 0));
    const safeTotal = Math.max(0, Number(total || 0));
    if (safeTotal <= 0) return 0;
    if (safeCompleted >= safeTotal) return 100;
    return Math.max(0, Math.floor((safeCompleted / safeTotal) * 100));
  };

  const counselors = rows<SqlRow>(
    `
      SELECT email, name, department, year_level, last_login, last_activity
      FROM users
      WHERE LOWER(COALESCE(role, '')) = 'counselor'
      ORDER BY name ASC
    `,
  );

  const studentStatsByCounselor = new Map<string, { student_count: number; students_with_phone: number }>();
  for (const item of rows<{ counselor_email: string; student_count: number; students_with_phone: number }>(
    `
      SELECT LOWER(TRIM(counselor_email)) AS counselor_email,
             COUNT(*) AS student_count,
             SUM(CASE WHEN COALESCE(TRIM(parent_phone), '') <> '' THEN 1 ELSE 0 END) AS students_with_phone
      FROM counselor_students
      WHERE COALESCE(is_active, 1) = 1
      GROUP BY LOWER(TRIM(counselor_email))
    `,
  )) {
    studentStatsByCounselor.set(String(item.counselor_email || '').trim().toLowerCase(), {
      student_count: Number(item.student_count || 0),
      students_with_phone: Number(item.students_with_phone || 0),
    });
  }

  const messageStatsByCounselor = new Map<string, {
    total_messages: number;
    week_messages: number;
    unique_students_messaged: number;
  }>();
  for (const item of rows<{ counselor_email: string; total_messages: number; week_messages: number; unique_students_messaged: number }>(
    `
      SELECT LOWER(TRIM(counselor_email)) AS counselor_email,
             COUNT(*) AS total_messages,
             SUM(CASE WHEN sent_at >= datetime('now', '-7 days') THEN 1 ELSE 0 END) AS week_messages,
             COUNT(DISTINCT REPLACE(UPPER(TRIM(reg_no)), '.0', '')) AS unique_students_messaged
      FROM sent_messages
      GROUP BY LOWER(TRIM(counselor_email))
    `,
  )) {
    messageStatsByCounselor.set(String(item.counselor_email || '').trim().toLowerCase(), {
      total_messages: Number(item.total_messages || 0),
      week_messages: Number(item.week_messages || 0),
      unique_students_messaged: Number(item.unique_students_messaged || 0),
    });
  }

  const testsUploadedByCounselor = new Map<string, number>();
  for (const item of rows<{ counselor_email: string; tests_uploaded: number }>(
    `
      SELECT LOWER(TRIM(u.email)) AS counselor_email,
             COUNT(DISTINCT tm.test_id) AS tests_uploaded
      FROM users u
      LEFT JOIN counselor_students cs
        ON LOWER(TRIM(cs.counselor_email)) = LOWER(TRIM(u.email))
       AND COALESCE(cs.is_active, 1) = 1
      LEFT JOIN student_marks sm
        ON REPLACE(UPPER(TRIM(cs.reg_no)), '.0', '') = REPLACE(UPPER(TRIM(sm.reg_no)), '.0', '')
      LEFT JOIN test_metadata tm
        ON tm.test_id = sm.test_id
       AND UPPER(COALESCE(tm.department, '')) = UPPER(COALESCE(u.department, ''))
       AND COALESCE(tm.year_level, 1) = COALESCE(u.year_level, 1)
      WHERE LOWER(COALESCE(u.role, '')) = 'counselor'
      GROUP BY LOWER(TRIM(u.email))
    `,
  )) {
    testsUploadedByCounselor.set(
      String(item.counselor_email || '').trim().toLowerCase(),
      Number(item.tests_uploaded || 0),
    );
  }

  return counselors.map((item) => {
    const email = String(item.email || '').trim().toLowerCase();
    const department = String(item.department || '').trim().toUpperCase() || 'N/A';
    const yearLevel = Number(item.year_level || 1) || 1;
    const studentStats = studentStatsByCounselor.get(email);
    const messageStats = messageStatsByCounselor.get(email);
    const studentCount = Number(studentStats?.student_count || 0);
    const studentsWithPhone = Number(studentStats?.students_with_phone || 0);
    const testsUploaded = Number(testsUploadedByCounselor.get(email) || 0);
    const totalMessages = Number(messageStats?.total_messages || 0);
    const weekMessages = Number(messageStats?.week_messages || 0);
    const uniqueStudentsMessaged = Number(messageStats?.unique_students_messaged || 0);

    let workStatus: CounselorActivitySummaryRow['work_status'] = 'Not Started';
    if (studentCount > 0 && testsUploaded > 0 && totalMessages > 0) workStatus = 'Complete';
    else if (studentCount > 0 && testsUploaded > 0) workStatus = 'Partial - No Reports Sent';
    else if (studentCount > 0) workStatus = 'Partial - No Tests Uploaded';

    return {
      email,
      name: String(item.name || email),
      department,
      year_level: yearLevel,
      last_login: String(item.last_login || ''),
      last_activity: String(item.last_activity || ''),
      student_count: studentCount,
      students_with_phone: studentsWithPhone,
      tests_uploaded: testsUploaded,
      total_messages: totalMessages,
      week_messages: weekMessages,
      unique_students_messaged: uniqueStudentsMessaged,
      work_status: workStatus,
      completion_pct: toPercentInt(Math.min(uniqueStudentsMessaged, studentCount), studentCount),
    } satisfies CounselorActivitySummaryRow;
  });
}

export function logMessage(
  counselorEmail: string,
  regNo: string,
  studentName: string,
  message: string,
  format = 'message',
  whatsappLink = '',
  options?: {
    test_id?: number | null;
    status?: string;
    delivery_status?: string;
    error_message?: string | null;
    send_mode?: string;
  },
) {
  db.prepare(`
    INSERT INTO sent_messages
    (counselor_email, test_id, reg_no, student_name, message, format, status, delivery_status, whatsapp_link, error_message, session_id, send_mode)
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
  `).run(
    counselorEmail,
    options?.test_id ?? null,
    regNo,
    studentName,
    message,
    format,
    options?.status || 'sent',
    options?.delivery_status || 'pending',
    whatsappLink,
    options?.error_message || null,
    null,
    options?.send_mode || 'app',
  );
}

export function logNoticeDelivery(
  counselorEmail: string,
  noticeId: number,
  regNo: string,
  studentName: string,
  message: string,
  options?: {
    whatsapp_link?: string;
    status?: string;
    delivery_status?: string;
    error_message?: string | null;
    send_mode?: string;
  },
) {
  db.prepare(`
    INSERT INTO notice_deliveries
    (notice_id, counselor_email, reg_no, student_name, message, status, delivery_status, whatsapp_link, error_message, send_mode)
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    ON CONFLICT(notice_id, counselor_email, reg_no) DO UPDATE SET
      student_name = excluded.student_name,
      message = excluded.message,
      sent_at = CURRENT_TIMESTAMP,
      status = excluded.status,
      delivery_status = excluded.delivery_status,
      whatsapp_link = excluded.whatsapp_link,
      error_message = excluded.error_message,
      send_mode = excluded.send_mode
  `).run(
    noticeId,
    String(counselorEmail || '').trim().toLowerCase(),
    String(regNo || '').trim(),
    String(studentName || '').trim(),
    String(message || '').trim(),
    options?.status || 'sent',
    options?.delivery_status || 'pending',
    options?.whatsapp_link || '',
    options?.error_message || null,
    options?.send_mode || 'app',
  );
}

export function findExistingDepartmentYearTest(
  department: string,
  yearLevel: number,
  semester: string,
  testName: string,
  batchName = '',
) {
  const existing = row<SqlRow>(
    `
      SELECT tm.test_id, tm.file_hash, tm.uploaded_by, tm.uploaded_at
      FROM test_metadata tm
      WHERE LOWER(COALESCE(tm.department, '')) = LOWER(COALESCE(?, ''))
        AND COALESCE(tm.year_level, 1) = COALESCE(?, 1)
        AND LOWER(COALESCE(tm.semester, '')) = LOWER(COALESCE(?, ''))
        AND LOWER(COALESCE(tm.test_name, '')) = LOWER(COALESCE(?, ''))
        AND LOWER(COALESCE(tm.batch_name, '')) = LOWER(COALESCE(?, ''))
      ORDER BY tm.uploaded_at DESC, tm.test_id DESC
      LIMIT 1
    `,
    [department, Number(yearLevel || 1), String(semester || ''), testName, batchName || ''],
  );

  if (!existing) return null;
  return {
    test_id: Number(existing.test_id || 0),
    file_hash: String(existing.file_hash || ''),
    uploaded_by: String(existing.uploaded_by || ''),
    uploaded_at: String(existing.uploaded_at || ''),
  } satisfies ExistingScopedTestRecord;
}

function getOrCreateBatch(name: string) {
  const batchName = String(name || '').trim();
  const existing = row<{ id: number }>('SELECT id FROM batches WHERE name = ?', [batchName]);
  if (existing?.id) return Number(existing.id);

  const parts = batchName.split('-');
  const startYear = /^\d{4}$/.test(parts[0] || '') ? Number(parts[0]) : new Date().getFullYear();
  const endYear = startYear + 1;
  const result = db.prepare('INSERT INTO batches (name, start_year, end_year) VALUES (?, ?, ?)').run(batchName, startYear, endYear);
  return Number(result.lastInsertRowid);
}

function getOrCreateSemester(batchId: number, semesterNumber: number) {
  const existing = row<{ id: number }>('SELECT id FROM semesters WHERE batch_id = ? AND semester_number = ?', [batchId, semesterNumber]);
  if (existing?.id) return Number(existing.id);

  const result = db.prepare('INSERT INTO semesters (batch_id, semester_number) VALUES (?, ?)').run(batchId, semesterNumber);
  return Number(result.lastInsertRowid);
}

function createTest(semesterId: number, testName: string) {
  const result = db.prepare('INSERT INTO tests (semester_id, test_name, max_marks) VALUES (?, ?, ?)').run(semesterId, testName, 100);
  return Number(result.lastInsertRowid);
}

function replaceTestContent(testId: number, semesterId: number, testName: string) {
  db.prepare('DELETE FROM student_marks WHERE test_id = ?').run(testId);
  db.prepare('DELETE FROM test_metadata WHERE test_id = ?').run(testId);
  db.prepare('UPDATE tests SET semester_id = ?, test_name = ? WHERE id = ?').run(semesterId, testName, testId);
}

function insertTestMetadata(
  testId: number,
  metadata: {
    batch_name: string;
    semester: string;
    year_level: number;
    test_name: string;
    department: string;
    section: string;
    file_hash: string;
    subjects: string[];
    uploaded_by: string;
  },
) {
  db.prepare(`
    INSERT OR REPLACE INTO test_metadata (
      test_id, batch_name, semester, year_level, test_name, department, section, file_hash, is_blocked, academic_year,
      subjects, subject_columns, header_row, data_start_row, uploaded_at, uploaded_by
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
  `).run(
    testId,
    metadata.batch_name,
    metadata.semester,
    metadata.year_level,
    metadata.test_name,
    metadata.department,
    metadata.section,
    metadata.file_hash,
    0,
    null,
    JSON.stringify(metadata.subjects || []),
    JSON.stringify({}),
    null,
    7,
    new Date().toISOString().slice(0, 19).replace('T', ' '),
    metadata.uploaded_by,
  );
}

function insertStudentMarks(
  testId: number,
  marksData: Array<{
    reg_no: string;
    student_name: string;
    subject_name: string;
    subject_code: string;
    marks: string;
    department: string;
    section?: string;
  }>,
  uploadedBy: string,
) {
  const stmt = db.prepare(`
    INSERT OR REPLACE INTO student_marks
    (test_id, reg_no, student_name, subject_name, subject_code, marks, department, section, uploaded_by)
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
  `);

  for (const mark of marksData) {
    const subjectName = String(mark.subject_name || '').trim();
    if (!subjectName || isAttendanceField(subjectName)) continue;
    stmt.run(
      testId,
      String(mark.reg_no || ''),
      String(mark.student_name || ''),
      subjectName,
      String(mark.subject_code || ''),
      String(mark.marks ?? ''),
      String(mark.department || ''),
      String(mark.section || ''),
      uploadedBy,
    );
  }
}

export function saveUploadedTestMarks(payload: {
  test_name: string;
  semester: string;
  counselor_email: string;
  students: Array<{
    reg_no: string;
    name: string;
    department?: string;
    marks: Record<string, string>;
    section?: string;
  }>;
  subjects: string[];
  batch_name?: string;
  department?: string;
  section?: string;
  file_hash?: string;
  replace_test_id?: number | null;
  year_level: number;
  uploaded_by?: string;
}) {
  const cleanedSubjects: string[] = [];
  const seenSubjects = new Set<string>();
  for (const subject of payload.subjects || []) {
    const subjectName = String(subject || '').trim();
    if (!subjectName || isAttendanceField(subjectName)) continue;
    const subjectKey = normalizeMetricKey(subjectName);
    if (seenSubjects.has(subjectKey)) continue;
    seenSubjects.add(subjectKey);
    cleanedSubjects.push(subjectName);
  }

  if (!cleanedSubjects.length) {
    throw new Error('No valid subject columns found after excluding attendance fields.');
  }

  const config = getAppConfig();
  const chosenBatchName = String(payload.batch_name || '').trim() || getBatchNameForYearLevel(payload.year_level, config);
  let semesterNumber = 1;
  try {
    const digits = String(payload.semester || '').replace(/\D/g, '');
    semesterNumber = Number(digits || '1') || 1;
  } catch {
    semesterNumber = 1;
  }

  const batchId = getOrCreateBatch(chosenBatchName);
  const semesterId = getOrCreateSemester(batchId, semesterNumber);
  const resolvedDepartment =
    String(payload.department || '').trim() ||
    String(payload.students.find((student) => String(student.department || '').trim())?.department || '').trim();
  const resolvedSection = String(payload.section || '').trim();

  const transaction = db.transaction(() => {
    const testId = payload.replace_test_id ? Number(payload.replace_test_id) : createTest(semesterId, payload.test_name);
    if (payload.replace_test_id) {
      replaceTestContent(testId, semesterId, payload.test_name);
    }

    insertTestMetadata(testId, {
      batch_name: chosenBatchName,
      semester: String(payload.semester || '').trim(),
      year_level: Number(payload.year_level || 1) || 1,
      test_name: payload.test_name,
      department: resolvedDepartment,
      section: resolvedSection,
      file_hash: String(payload.file_hash || ''),
      subjects: cleanedSubjects,
      uploaded_by: String(payload.uploaded_by || payload.counselor_email || ''),
    });

    const marksData = payload.students.flatMap((student) =>
      cleanedSubjects.map((subject) => ({
        reg_no: String(student.reg_no || ''),
        student_name: String(student.name || ''),
        subject_name: subject,
        subject_code: '',
        marks: String(student.marks?.[subject] ?? ''),
        department: String(student.department || resolvedDepartment || ''),
        section: String(student.section || resolvedSection || ''),
      })),
    );

    insertStudentMarks(testId, marksData, String(payload.counselor_email || ''));
    return testId;
  });

  const testId = transaction();
  return {
    testId,
    message: `Saved marks for ${payload.students.length} students`,
  };
}

function isSummaryMetricSubject(name: string) {
  const value = String(name || '').trim().toLowerCase();
  const normalized = value.replace(/[^a-z0-9]/g, '');
  return new Set([
    'gpa',
    'cgpa',
    'failed',
    'fail',
    'noofsubjectsfailed',
    'failedsubjects',
    'absentees',
    'absentee',
    'absentstudents',
    'absentcount',
    'noofsubjectsabsent',
  ]).has(normalized);
}

export function getVisibleReportSubjects(subjects: string[]) {
  return (subjects || []).filter((subject) => !isSummaryMetricSubject(subject));
}

export function getTestMetadata(testId: number) {
  return row<SqlRow>('SELECT * FROM test_metadata WHERE test_id = ?', [testId]);
}

export function updateTestMetadataFields(
  testId: number,
  fields: {
    test_name?: string;
    semester?: string;
    department?: string;
    batch_name?: string;
    section?: string;
  },
) {
  const sets: string[] = [];
  const values: unknown[] = [];
  let nextSemester = '';
  let nextBatchName = '';

  for (const [key, value] of Object.entries(fields)) {
    if (value === undefined) continue;
    sets.push(`${key} = ?`);
    values.push(value);
    if (key === 'semester') nextSemester = String(value || '').trim();
    if (key === 'batch_name') nextBatchName = String(value || '').trim();
  }

  if (!sets.length) return true;

  const transaction = db.transaction(() => {
    values.push(testId);
    db.prepare(`UPDATE test_metadata SET ${sets.join(', ')} WHERE test_id = ?`).run(...values);

    const currentMeta = getTestMetadata(testId) || {};
    const resolvedBatchName = nextBatchName || String(currentMeta.batch_name || '').trim();
    const resolvedSemester = nextSemester || String(currentMeta.semester || '').trim();
    const resolvedTestName = fields.test_name !== undefined ? String(fields.test_name || '').trim() : String(currentMeta.test_name || '').trim();

    const semesterDigits = resolvedSemester.replace(/\D/g, '');
    const semesterNumber = Number(semesterDigits || '1') || 1;
    const batchId = getOrCreateBatch(resolvedBatchName);
    const semesterId = getOrCreateSemester(batchId, semesterNumber);
    db.prepare('UPDATE tests SET semester_id = ?, test_name = ? WHERE id = ?').run(semesterId, resolvedTestName, testId);
  });

  transaction();
  return true;
}

export function updateTestBlockStatus(testId: number, isBlocked: boolean) {
  db.prepare('UPDATE test_metadata SET is_blocked = ? WHERE test_id = ?').run(isBlocked ? 1 : 0, testId);
  return true;
}

function deleteTestDependencies(testId: number) {
  db.prepare('DELETE FROM counselor_mark_overrides WHERE test_id = ?').run(testId);
  db.prepare('DELETE FROM sent_messages WHERE test_id = ?').run(testId);
  db.prepare('DELETE FROM student_marks WHERE test_id = ?').run(testId);
  db.prepare('DELETE FROM test_metadata WHERE test_id = ?').run(testId);
}

export function deleteTest(testId: number) {
  const transaction = db.transaction((id: number) => {
    deleteTestDependencies(id);
    db.prepare('DELETE FROM tests WHERE id = ?').run(id);
  });
  transaction(testId);
  return true;
}

export function upsertTestMark(
  testId: number,
  regNo: string,
  subjectName: string,
  marks: string,
  department = '',
  uploadedBy = '',
) {
  const subject = String(subjectName || '').trim();
  if (!subject || isAttendanceField(subject)) return;
  const resolvedSection = String(
    row<{ section?: string }>(
      `
        SELECT COALESCE(
          (
            SELECT NULLIF(sm.section, '')
            FROM student_marks sm
            WHERE sm.test_id = ? AND sm.reg_no = ? AND sm.subject_name = ?
            LIMIT 1
          ),
          (
            SELECT tm.section
            FROM test_metadata tm
            WHERE tm.test_id = ?
            LIMIT 1
          ),
          ''
        ) AS section
      `,
      [testId, regNo, subject, testId],
    )?.section || '',
  ).trim();

  db.prepare(`
    INSERT INTO student_marks (test_id, reg_no, student_name, subject_name, subject_code, marks, department, section, uploaded_by)
    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
    ON CONFLICT(test_id, reg_no, subject_name)
    DO UPDATE SET marks = excluded.marks, department = excluded.department, section = excluded.section, uploaded_by = excluded.uploaded_by
  `).run(testId, regNo, '', subject, '', String(marks || ''), String(department || ''), resolvedSection, String(uploadedBy || ''));
}

export function upsertCounselorMarkOverride(
  counselorEmail: string,
  testId: number,
  regNo: string,
  subjectName: string,
  marks: string,
) {
  const email = String(counselorEmail || '').trim().toLowerCase();
  const subject = String(subjectName || '').trim();
  const normalizedRegNo = String(regNo || '').trim();
  if (!email || !normalizedRegNo || !subject || isAttendanceField(subject)) return;
  db.prepare(`
    INSERT INTO counselor_mark_overrides (counselor_email, test_id, reg_no, subject_name, marks)
    VALUES (?, ?, ?, ?, ?)
    ON CONFLICT(counselor_email, test_id, reg_no, subject_name)
    DO UPDATE SET marks = excluded.marks, updated_at = CURRENT_TIMESTAMP
  `).run(email, testId, normalizedRegNo, subject, String(marks || ''));
}

export function getTestMarksGrouped(testId: number) {
  const rowsForMarks = rows<SqlRow>(
    `
      SELECT DISTINCT
        sm.reg_no,
        sm.subject_name,
        sm.marks,
        COALESCE(
          NULLIF(sm.section, ''),
          (
            SELECT tm.section
            FROM test_metadata tm
            WHERE tm.test_id = sm.test_id
            LIMIT 1
          ),
          ''
        ) AS resolved_section,
        COALESCE(
          NULLIF(sm.department, ''),
          (
            SELECT cs.department
            FROM counselor_students cs
            WHERE UPPER(TRIM(cs.reg_no)) = UPPER(TRIM(sm.reg_no))
              AND TRIM(COALESCE(cs.department, '')) <> ''
            ORDER BY cs.id DESC
            LIMIT 1
          ),
          (
            SELECT tm.department
            FROM test_metadata tm
            WHERE tm.test_id = sm.test_id
            LIMIT 1
          ),
          ''
        ) AS resolved_department,
        COALESCE(
          NULLIF(sm.student_name, ''),
          (
            SELECT cs.student_name
            FROM counselor_students cs
            WHERE UPPER(TRIM(cs.reg_no)) = UPPER(TRIM(sm.reg_no))
            ORDER BY cs.id DESC
            LIMIT 1
          ),
          (
            SELECT s2.student_name
            FROM sent_messages s2
            WHERE s2.test_id = sm.test_id
              AND UPPER(TRIM(s2.reg_no)) = UPPER(TRIM(sm.reg_no))
              AND COALESCE(TRIM(s2.student_name), '') <> ''
            ORDER BY s2.sent_at DESC
            LIMIT 1
          ),
          ''
        ) AS student_name
      FROM student_marks sm
      WHERE sm.test_id = ?
      ORDER BY sm.reg_no, sm.subject_name
    `,
    [testId],
  );

  const meta = row<SqlRow>('SELECT subjects, department FROM test_metadata WHERE test_id = ?', [testId]);
  const fallbackDepartment = String(meta?.department || '').trim();

  let subjects: string[] = [];
  const isNamedSubject = (name: unknown) => {
    const text = String(name || '').trim();
    if (!text) return false;
    if (isAttendanceField(text)) return false;
    const lower = text.toLowerCase();
    if (lower.startsWith('unnamed')) return false;
    if (/^subject[_\s-]*\d+$/.test(lower)) return false;
    return true;
  };

  if (meta?.subjects) {
    try {
      const parsed = JSON.parse(String(meta.subjects || '[]'));
      subjects = parsed.filter((subject: string) => isNamedSubject(subject));
    } catch {
      subjects = [];
    }
  }

  if (!subjects.length) {
    subjects = Array.from(
      new Set(
        rowsForMarks
          .map((rowItem) => String(rowItem.subject_name || '').trim())
          .filter((subject) => isNamedSubject(subject)),
      ),
    ).sort();
  }

  const students = new Map<string, { reg_no: string; student_name: string; department: string; section: string; marks: Record<string, string> }>();
  for (const rowItem of rowsForMarks) {
    const regNo = String(rowItem.reg_no || '').trim();
    const subjectName = String(rowItem.subject_name || '').trim();
    if (!regNo || isAttendanceField(subjectName)) continue;

    const resolvedDepartment = String(rowItem.resolved_department || fallbackDepartment || '').trim();
    const resolvedSection = String(rowItem.resolved_section || '').trim();
    if (!students.has(regNo)) {
      students.set(regNo, {
        reg_no: regNo,
        student_name: String(rowItem.student_name || '').trim(),
        department: resolvedDepartment,
        section: resolvedSection,
        marks: {},
      });
    }

    const student = students.get(regNo)!;
    if (!student.department && resolvedDepartment) {
      student.department = resolvedDepartment;
    }
    if (!student.section && resolvedSection) {
      student.section = resolvedSection;
    }
    student.marks[subjectName] = String(rowItem.marks ?? '');
  }

  return {
    subjects,
    students: Array.from(students.values()),
  };
}

function normalizeNotificationUserEmail(value: string) {
  return normalizeLoginEmail(value);
}

function normalizeNotificationKey(value: unknown) {
  return String(value || '').trim();
}

export function getNotificationStatesForUser(userEmail: string) {
  const safeEmail = normalizeNotificationUserEmail(userEmail);
  if (!safeEmail) return { readKeys: [] as string[], deletedKeys: [] as string[] };
  const stateRows = rows<{ notification_key: string; status: string }>(
    'SELECT notification_key, status FROM notification_states WHERE user_email = ?',
    [safeEmail],
  );
  const readKeys: string[] = [];
  const deletedKeys: string[] = [];
  for (const state of stateRows) {
    const key = normalizeNotificationKey(state.notification_key);
    if (!key) continue;
    const status = String(state.status || 'read').trim().toLowerCase();
    if (status === 'deleted') {
      deletedKeys.push(key);
      readKeys.push(key);
    } else {
      readKeys.push(key);
    }
  }
  return {
    readKeys: Array.from(new Set(readKeys)),
    deletedKeys: Array.from(new Set(deletedKeys)),
  };
}

export function updateNotificationStatesForUser(userEmail: string, notificationKeys: unknown[], status: 'read' | 'deleted') {
  const safeEmail = normalizeNotificationUserEmail(userEmail);
  if (!safeEmail) return;
  const uniqueKeys = Array.from(new Set(notificationKeys.map(normalizeNotificationKey).filter(Boolean))).slice(0, 200);
  if (!uniqueKeys.length) return;
  const stmt = db.prepare(`
    INSERT INTO notification_states (user_email, notification_key, status, updated_at)
    VALUES (?, ?, ?, CURRENT_TIMESTAMP)
    ON CONFLICT(user_email, notification_key)
    DO UPDATE SET status = excluded.status, updated_at = CURRENT_TIMESTAMP
  `);
  const transaction = db.transaction((keys: string[]) => {
    for (const key of keys) stmt.run(safeEmail, key, status);
  });
  transaction(uniqueKeys);
}

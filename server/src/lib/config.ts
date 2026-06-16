import { config as loadEnv } from 'dotenv';
import { readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const currentDir = dirname(fileURLToPath(import.meta.url));
export const SERVER_ROOT = resolve(currentDir, '..', '..');
export const REWRITE_ROOT = resolve(SERVER_ROOT, '..');
export const DATA_ROOT = resolve(REWRITE_ROOT, 'data');
export const NOTICE_UPLOAD_ROOT = resolve(DATA_ROOT, 'notice_assets');
export const BACKUP_DIR = resolve(DATA_ROOT, 'backups');
export const ARCHIVE_DIR = resolve(DATA_ROOT, 'archives');
export const DESKTOP_INSTALLER_ROOT = resolve(DATA_ROOT, 'desktop-installer');
export const APP_ENV_FILE = resolve(REWRITE_ROOT, '.env');
loadEnv({ path: APP_ENV_FILE });

function readRootPackageVersion() {
  try {
    const rootPackage = JSON.parse(readFileSync(resolve(REWRITE_ROOT, 'package.json'), 'utf8')) as { version?: string };
    return String(rootPackage.version || '').trim() || '0.1.0';
  } catch {
    return '0.1.0';
  }
}

export const SHINE_DB_PATH = process.env.SHINE_DB_PATH || resolve(DATA_ROOT, 'rmkcet.db');
export const APP_NAME = 'RMKCET SHINE';
export const APP_VERSION = readRootPackageVersion();
export const DEFAULT_SYSTEM_ADMIN_EMAIL = process.env.DEFAULT_SYSTEM_ADMIN_EMAIL || 'admin@rmkcet.ac.in';
export const DEFAULT_SYSTEM_ADMIN_PASSWORD = process.env.DEFAULT_SYSTEM_ADMIN_PASSWORD || 'admin123';
export const SESSION_COOKIE = 'shine_sid';
export const TEST_MODE_COOKIE = 'shine_test_mode_email';
export const GOOGLE_STATE_COOKIE = 'shine_google_state';
export const GOOGLE_LOGIN_CONFLICT_COOKIE = 'shine_google_login_conflict';
export const LOGIN_OTP_COOKIE = 'shine_login_otp';
export const LOGIN_ROLE_COOKIE = 'shine_login_role_select';
export const PASSWORD_RESET_COOKIE = 'shine_password_reset';
export const SELF_RESET_OTP_COOKIE = 'shine_self_reset_otp';
export const SESSION_NOTICE_COOKIE = 'shine_session_notice';
export const ARCHIVE_VIEW_COOKIE = 'shine_archive_view';
export const SERVER_HOST = process.env.HOST || '::1';
export const CLIENT_ORIGIN = process.env.CLIENT_ORIGIN || 'http://[::1]:5000';
export const DESKTOP_SHELL_ORIGIN = process.env.DESKTOP_SHELL_ORIGIN || 'http://[::1]:5123';
export const CLIENT_ORIGINS = Array.from(new Set([
  CLIENT_ORIGIN,
  DESKTOP_SHELL_ORIGIN,
  ...String(process.env.CLIENT_ORIGINS || '')
    .split(',')
    .map((value) => value.trim())
    .filter(Boolean),
]));
export const SERVER_ORIGIN = process.env.SERVER_ORIGIN || 'http://[::1]:5001';
export const SERVER_PORT = Number(process.env.PORT || 5001);
export const COUNTRY_CODE = process.env.COUNTRY_CODE || '91';

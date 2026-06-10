import { config as loadEnv } from 'dotenv';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const currentDir = dirname(fileURLToPath(import.meta.url));
export const SERVER_ROOT = resolve(currentDir, '..', '..');
export const REWRITE_ROOT = resolve(SERVER_ROOT, '..');
export const DATA_ROOT = resolve(REWRITE_ROOT, 'data');
export const NOTICE_UPLOAD_ROOT = resolve(DATA_ROOT, 'notice_assets');
export const BACKUP_DIR = resolve(DATA_ROOT, 'backups');
export const ARCHIVE_DIR = resolve(DATA_ROOT, 'archives');
export const APP_ENV_FILE = resolve(REWRITE_ROOT, '.env');
loadEnv({ path: APP_ENV_FILE });

export const SHINE_DB_PATH = process.env.SHINE_DB_PATH || resolve(DATA_ROOT, 'rmkcet.db');
export const APP_NAME = 'RMKCET SHINE';
export const APP_VERSION = '0.1.0-rebuild';
export const DEFAULT_SYSTEM_ADMIN_EMAIL = process.env.DEFAULT_SYSTEM_ADMIN_EMAIL || 'admin@rmkcet.ac.in';
export const SESSION_COOKIE = 'shine_sid';
export const TEST_MODE_COOKIE = 'shine_test_mode_email';
export const GOOGLE_STATE_COOKIE = 'shine_google_state';
export const LOGIN_OTP_COOKIE = 'shine_login_otp';
export const PASSWORD_RESET_COOKIE = 'shine_password_reset';
export const SELF_RESET_OTP_COOKIE = 'shine_self_reset_otp';
export const SERVER_HOST = process.env.HOST || '::1';
export const CLIENT_ORIGIN = process.env.CLIENT_ORIGIN || 'http://[::1]:5000';
export const SERVER_ORIGIN = process.env.SERVER_ORIGIN || 'http://[::1]:5001';
export const SERVER_PORT = Number(process.env.PORT || 5001);
export const COUNTRY_CODE = process.env.COUNTRY_CODE || '91';

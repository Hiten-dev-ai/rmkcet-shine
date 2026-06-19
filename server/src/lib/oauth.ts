import { CLIENT_ORIGIN, SERVER_ORIGIN } from './config.js';
import { getAppConfig } from './db.js';

function normalizeGoogleRedirectBaseUrl(value: string) {
  return String(value || '')
    .trim()
    .replace(/\/+$/, '')
    .replace(/\/auth\/google\/callback$/i, '');
}

export interface GoogleOauthSettings {
  enabled: boolean;
  requested: boolean;
  clientId: string;
  clientSecret: string;
  allowedDomain: string;
  redirectBaseUrl: string;
}

export function getGoogleOauthSettings(config = getAppConfig()): GoogleOauthSettings {
  const clientId = String(config.google_oauth_client_id || '').trim();
  const clientSecret = String(config.google_oauth_client_secret || '').trim();
  const allowedDomain = String(config.google_oauth_allowed_domain || '')
    .trim()
    .toLowerCase()
    .replace(/^@/, '');
  const redirectBaseUrl = normalizeGoogleRedirectBaseUrl(String(config.public_app_base_url || config.google_oauth_redirect_base_url || ''));
  const requested = String(config.google_oauth_enabled || 'false').trim().toLowerCase() === 'true';

  return {
    enabled: !!(requested && clientId && clientSecret),
    requested,
    clientId,
    clientSecret,
    allowedDomain,
    redirectBaseUrl,
  };
}

export function buildGoogleOauthRedirectUri(config = getAppConfig()) {
  const settings = getGoogleOauthSettings(config);
  const base = settings.redirectBaseUrl || SERVER_ORIGIN;
  return `${base}/auth/google/callback`;
}

export function buildGoogleOauthClientRedirect() {
  return `${CLIENT_ORIGIN}/?auth=google`;
}

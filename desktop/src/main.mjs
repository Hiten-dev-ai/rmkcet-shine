import http from 'node:http';
import https from 'node:https';
import { spawn, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { createReadStream, existsSync, mkdirSync, readFileSync } from 'node:fs';
import { access, mkdir, readFile, stat, writeFile } from 'node:fs/promises';
import { constants as fsConstants } from 'node:fs';
import { createRequire } from 'node:module';
import { dirname, extname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
const require = createRequire(import.meta.url);
const electron = require('electron');
const { autoUpdater } = require('electron-updater');

const { app, BrowserWindow, Menu, Notification, Tray, dialog, nativeImage, screen, shell, ipcMain } = electron;
const EmbeddedBrowserView = electron.BrowserView || electron.WebContentsView;

const currentDir = dirname(fileURLToPath(import.meta.url));
const desktopRoot = resolve(currentDir, '..');
const repoRoot = resolve(desktopRoot, '..');
const WHATSAPP_DESKTOP_APP_ID = '5319275A.WhatsAppDesktop_cv1g1gvanyjgm!App';
const APP_USER_MODEL_ID = String(process.env.SHINE_DESKTOP_APP_ID || 'dev.rmkcet.shine').trim();
const DEFAULT_LOCATOR_CSV_URL = 'https://drive.google.com/uc?export=download&id=1K1YZVkPF42X2F5oA6_ZQYfrB57JHhxma';
const packagedReleaseConfigPath = resolve(process.resourcesPath, 'release-config.json');
const isPackagedDesktopApp = app.isPackaged;
const desktopSettingsPath = resolve(app.getPath('userData'), 'desktop-settings.json');
const desktopUpdateRoot = resolve(app.getPath('userData'), 'updates');
const desktopUpdateStatusHtmlPath = resolve(app.getPath('userData'), 'update-status.html');
const desktopDiagnosticsLogPath = resolve(app.getPath('userData'), 'desktop-diagnostics.log');
const desktopAppLock = app.requestSingleInstanceLock();

const DEFAULT_DESKTOP_SETTINGS = {
  launchAtWindowsStartup: true,
  startMinimizedToTrayOnLogin: true,
  minimizeToTrayOnClose: true,
  desktopNotificationsEnabled: true,
  updateChecksEnabled: true,
  autoInstallUpdatesWhenIdle: true,
  notificationPollMinutes: 30,
  currentServerOriginOverride: '',
  locatorCsvUrl: DEFAULT_LOCATOR_CSV_URL,
  releaseChannelBaseUrl: '',
  downloadPageUrl: '',
  higherOfficialDigestDay: 'monday',
  higherOfficialDigestScope: 'allocated',
};

function readPackagedReleaseConfig() {
  if (!isPackagedDesktopApp || !existsSync(packagedReleaseConfigPath)) return null;
  try {
    const raw = JSON.parse(readFileSync(packagedReleaseConfigPath, 'utf8'));
    if (!raw || typeof raw !== 'object') return null;
    return raw;
  } catch {
    return null;
  }
}

const packagedReleaseConfig = readPackagedReleaseConfig();
const clientDistRoot = isPackagedDesktopApp
  ? resolve(process.resourcesPath, 'dist-desktop')
  : resolve(repoRoot, process.env.SHINE_DESKTOP_DIST_DIR || 'client/dist-desktop');
const desktopMode = isPackagedDesktopApp
  ? 'desktop-app'
  : process.env.SHINE_DESKTOP_MODE === 'desktop-app' ? 'desktop-app' : 'desktop-dev';
const devRendererUrl = String(process.env.SHINE_DESKTOP_DEV_URL || 'http://[::1]:5000').trim();
const packagedApiOrigin = String(packagedReleaseConfig?.apiOrigin || process.env.SHINE_DESKTOP_API_ORIGIN || 'http://[::1]:5001').trim();
let apiOrigin = packagedApiOrigin;

function normalizeHost(host) {
  return String(host || '').trim().replace(/^\[|\]$/g, '');
}

const defaultShellHost = (() => {
  if (desktopMode === 'desktop-app') return '127.0.0.1';
  try {
    return normalizeHost(new URL(apiOrigin).hostname || '127.0.0.1');
  } catch {
    return '127.0.0.1';
  }
})();

const shellHost = normalizeHost(process.env.SHINE_DESKTOP_SHELL_HOST || defaultShellHost) || defaultShellHost;
const shellPort = Number(process.env.SHINE_DESKTOP_SHELL_PORT || 5123);
const shellOriginHost = shellHost.includes(':') ? `[${shellHost}]` : shellHost;
const shellOrigin = `http://${shellOriginHost}:${shellPort}`;

process.env.SHINE_DESKTOP_MODE = desktopMode;
process.env.SHINE_DESKTOP_API_ORIGIN = apiOrigin;
process.env.SHINE_DESKTOP_SHELL_ORIGIN = shellOrigin;

const MIME_TYPES = {
  '.css': 'text/css; charset=utf-8',
  '.html': 'text/html; charset=utf-8',
  '.ico': 'image/x-icon',
  '.jpeg': 'image/jpeg',
  '.jpg': 'image/jpeg',
  '.js': 'text/javascript; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.png': 'image/png',
  '.svg': 'image/svg+xml',
  '.txt': 'text/plain; charset=utf-8',
  '.webp': 'image/webp',
  '.woff': 'font/woff',
  '.woff2': 'font/woff2',
};

const TARGET_LABELS = {
  default_browser: 'Default Browser',
  chrome: 'Google Chrome',
  edge: 'Microsoft Edge',
  whatsapp_desktop: 'WhatsApp Desktop',
};
const EMBEDDED_WHATSAPP_LABEL = 'Embedded Workspace';
const EMBEDDED_WHATSAPP_URL = 'https://web.whatsapp.com/';
const EMBEDDED_WHATSAPP_USER_AGENT = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/137.0.0.0 Safari/537.36';

let shellServer = null;
let mainWindowRef = null;
let desktopWorkspaceRestoreBounds = null;
let desktopWorkspaceActive = false;
let desktopWhatsappView = null;
let desktopWhatsappViewAttached = false;
let desktopWhatsappViewLoading = false;
let floatingSendWindow = null;
let floatingSendPayload = null;
let floatingSendCloseReason = 'closed';
let floatingSendResetOnNextShow = true;
let desktopWorkspaceBrowserSession = {
  target: null,
  debugPort: 0,
  profileDir: '',
  processNames: [],
};
const DESKTOP_WORKSPACE_MIN_WIDTH = 460;
const DESKTOP_WORKSPACE_MIN_HEIGHT = 760;
const DEFAULT_MAIN_MIN_WIDTH = 1180;
const DEFAULT_MAIN_MIN_HEIGHT = 760;
const WORKSPACE_BROWSER_DEBUG_PORTS = {
  chrome: 9333,
  edge: 9334,
};

function escapeHtml(value) {
  return String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function normalizeOrigin(value) {
  const raw = String(value || '').trim().replace(/\/+$/, '');
  if (!/^https?:\/\//i.test(raw)) return '';
  try {
    return new URL(raw).origin;
  } catch {
    return '';
  }
}

function sanitizeDesktopSettings(raw) {
  const source = raw && typeof raw === 'object' ? raw : {};
  return {
    ...DEFAULT_DESKTOP_SETTINGS,
    launchAtWindowsStartup: Boolean(source.launchAtWindowsStartup ?? DEFAULT_DESKTOP_SETTINGS.launchAtWindowsStartup),
    startMinimizedToTrayOnLogin: Boolean(source.startMinimizedToTrayOnLogin ?? DEFAULT_DESKTOP_SETTINGS.startMinimizedToTrayOnLogin),
    minimizeToTrayOnClose: Boolean(source.minimizeToTrayOnClose ?? DEFAULT_DESKTOP_SETTINGS.minimizeToTrayOnClose),
    desktopNotificationsEnabled: Boolean(source.desktopNotificationsEnabled ?? DEFAULT_DESKTOP_SETTINGS.desktopNotificationsEnabled),
    updateChecksEnabled: Boolean(source.updateChecksEnabled ?? DEFAULT_DESKTOP_SETTINGS.updateChecksEnabled),
    autoInstallUpdatesWhenIdle: Boolean(source.autoInstallUpdatesWhenIdle ?? DEFAULT_DESKTOP_SETTINGS.autoInstallUpdatesWhenIdle),
    notificationPollMinutes: Math.max(1, Math.min(120, Number(source.notificationPollMinutes || DEFAULT_DESKTOP_SETTINGS.notificationPollMinutes) || DEFAULT_DESKTOP_SETTINGS.notificationPollMinutes)),
    currentServerOriginOverride: normalizeOrigin(source.currentServerOriginOverride),
    locatorCsvUrl: String(source.locatorCsvUrl || packagedReleaseConfig?.locatorCsvUrl || process.env.SHINE_DESKTOP_LOCATOR_CSV_URL || DEFAULT_LOCATOR_CSV_URL).trim(),
    releaseChannelBaseUrl: String(source.releaseChannelBaseUrl || packagedReleaseConfig?.releaseChannelBaseUrl || '').trim(),
    downloadPageUrl: String(source.downloadPageUrl || packagedReleaseConfig?.downloadPageUrl || '').trim(),
    higherOfficialDigestDay: ['sunday', 'monday', 'tuesday', 'wednesday', 'thursday', 'friday', 'saturday'].includes(String(source.higherOfficialDigestDay || '').trim().toLowerCase())
      ? String(source.higherOfficialDigestDay).trim().toLowerCase()
      : 'monday',
    higherOfficialDigestScope: String(source.higherOfficialDigestScope || '').trim().toLowerCase() === 'all' ? 'all' : 'allocated',
  };
}

function enforceDesktopSettingsForRole(settings, role) {
  const safeRole = String(role || '').trim().toLowerCase();
  if (safeRole === 'admin') return settings;
  return {
    ...settings,
    updateChecksEnabled: true,
    autoInstallUpdatesWhenIdle: true,
  };
}

function readDesktopSettingsSync() {
  try {
    return sanitizeDesktopSettings(JSON.parse(readFileSync(desktopSettingsPath, 'utf8')));
  } catch {
    return sanitizeDesktopSettings({});
  }
}

async function writeDesktopSettings(nextSettings) {
  const sanitized = sanitizeDesktopSettings(nextSettings);
  await mkdir(dirname(desktopSettingsPath), { recursive: true });
  await writeFile(desktopSettingsPath, JSON.stringify(sanitized, null, 2), 'utf8');
  applyLoginItemSettings(sanitized);
  updateTrayMenu();
  return sanitized;
}

let desktopSettings = readDesktopSettingsSync();

function applyLoginItemSettings(settings = desktopSettings) {
  if (process.platform !== 'win32') return;
  try {
    const enabled = Boolean(settings.launchAtWindowsStartup);
    app.setLoginItemSettings({
      openAtLogin: enabled,
      path: process.execPath,
      args: enabled ? ['--hidden'] : [],
    });
  } catch {
    // Ignore unsupported startup registration failures.
  }
}

applyLoginItemSettings(desktopSettings);

function parseCsvLine(line) {
  const cells = [];
  let current = '';
  let quoted = false;
  for (let index = 0; index < line.length; index += 1) {
    const char = line[index];
    if (char === '"') {
      if (quoted && line[index + 1] === '"') {
        current += '"';
        index += 1;
      } else {
        quoted = !quoted;
      }
      continue;
    }
    if (char === ',' && !quoted) {
      cells.push(current.trim());
      current = '';
      continue;
    }
    current += char;
  }
  cells.push(current.trim());
  return cells;
}

function parseLocatorCsv(csvText) {
  const out = {};
  for (const rawLine of String(csvText || '').split(/\r?\n/)) {
    const line = rawLine.trim();
    if (!line || line.startsWith('#')) continue;
    const [key, ...rest] = parseCsvLine(line);
    const normalizedKey = String(key || '').trim();
    if (!normalizedKey || normalizedKey.toLowerCase() === 'key') continue;
    out[normalizedKey] = rest.join(',').trim();
  }
  return out;
}

async function fetchJson(url, timeoutMs = 6500) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    const response = await fetch(url, { signal: controller.signal, cache: 'no-store' });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return await response.json();
  } finally {
    clearTimeout(timer);
  }
}

async function fetchText(url, timeoutMs = 6500) {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    const response = await fetch(url, { signal: controller.signal, cache: 'no-store' });
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return await response.text();
  } finally {
    clearTimeout(timer);
  }
}

async function probeApiOrigin(origin, timeoutMs = 2500) {
  const safeOrigin = normalizeOrigin(origin);
  if (!safeOrigin) return false;
  try {
    await fetchJson(`${safeOrigin}/api/bootstrap`, timeoutMs);
    return true;
  } catch {
    return false;
  }
}

async function waitForApiOrigin(origin, attempts = 80, intervalMs = 500) {
  const safeOrigin = normalizeOrigin(origin);
  if (!safeOrigin) return false;
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    if (await probeApiOrigin(safeOrigin, 1200)) return true;
    await delay(intervalMs);
  }
  return false;
}

function getReleaseChannelBaseUrl() {
  return String(desktopSettings.releaseChannelBaseUrl || packagedReleaseConfig?.releaseChannelBaseUrl || '').trim()
    || `${apiOrigin}/api/desktop/installer`;
}

async function resolveServerOriginWithLocator() {
  const primary = normalizeOrigin(packagedApiOrigin);
  const shouldWaitForPrimary = !isPackagedDesktopApp || process.env.SHINE_DESKTOP_WAIT_FOR_PRIMARY === '1';
  const primaryOnline = primary && (
    shouldWaitForPrimary
      ? await waitForApiOrigin(primary, Number(process.env.SHINE_DESKTOP_PRIMARY_WAIT_ATTEMPTS || 80), 500)
      : await probeApiOrigin(primary)
  );
  if (primaryOnline) {
    apiOrigin = primary;
    return { online: true, apiOrigin, source: 'primary', locator: null, error: '' };
  }

  const override = normalizeOrigin(desktopSettings.currentServerOriginOverride);
  if (override && override !== primary && await probeApiOrigin(override)) {
    apiOrigin = override;
    return { online: true, apiOrigin, source: 'override', locator: null, error: '' };
  }

  const locatorCsvUrl = String(desktopSettings.locatorCsvUrl || packagedReleaseConfig?.locatorCsvUrl || process.env.SHINE_DESKTOP_LOCATOR_CSV_URL || '').trim();
  if (locatorCsvUrl) {
    try {
      const locator = parseLocatorCsv(await fetchText(locatorCsvUrl, 8000));
      const locatorOrigin = normalizeOrigin(locator.apiOrigin);
      if (locatorOrigin && await probeApiOrigin(locatorOrigin)) {
        desktopSettings = await writeDesktopSettings({
          ...desktopSettings,
          locatorCsvUrl,
          currentServerOriginOverride: locatorOrigin,
          releaseChannelBaseUrl: String(locator.releaseChannelBaseUrl || '').trim(),
          downloadPageUrl: String(locator.downloadPageUrl || '').trim(),
        });
        apiOrigin = locatorOrigin;
        return { online: true, apiOrigin, source: 'locator', locator, error: '' };
      }
      return { online: false, apiOrigin: primary || apiOrigin, source: 'offline', locator, error: 'Locator was reachable, but its server URL was not.' };
    } catch (error) {
      return { online: false, apiOrigin: primary || apiOrigin, source: 'offline', locator: null, error: error instanceof Error ? error.message : 'Locator lookup failed.' };
    }
  }

  return { online: false, apiOrigin: primary || apiOrigin, source: 'offline', locator: null, error: 'Primary server is unavailable and no locator CSV is configured.' };
}

let lastConnectivityState = {
  online: false,
  apiOrigin,
  source: 'unknown',
  locator: null,
  error: '',
};
let appTray = null;
let appIsQuitting = false;
let pendingUpdateInfo = null;
let updateInstallInProgress = false;
let desktopUpdateCheckTimer = null;
const cachedDesktopIconPaths = new Map();
const cachedDesktopIconImages = new Map();

if (!desktopAppLock) {
  app.quit();
}
app.setAppUserModelId(APP_USER_MODEL_ID);

function getDesktopIconPath(kind = 'window') {
  const cacheKey = String(kind || 'window');
  const cachedPath = cachedDesktopIconPaths.get(cacheKey);
  if (cachedPath && existsSync(cachedPath)) return cachedPath;
  const resourceRoot = process.resourcesPath || desktopRoot;
  const candidatesByKind = {
    notification: [
      resolve(resourceRoot, 'assets', 'icon.png'),
      resolve(desktopRoot, 'assets', 'icon.png'),
      resolve(resourceRoot, 'assets', 'icon.ico'),
      resolve(desktopRoot, 'assets', 'icon.ico'),
    ],
    tray: process.platform === 'win32' ? [
      resolve(resourceRoot, 'assets', 'icon.ico'),
      resolve(desktopRoot, 'assets', 'icon.ico'),
      resolve(resourceRoot, 'assets', 'icon.png'),
      resolve(desktopRoot, 'assets', 'icon.png'),
    ] : [
      resolve(resourceRoot, 'assets', 'icon.png'),
      resolve(desktopRoot, 'assets', 'icon.png'),
      resolve(resourceRoot, 'assets', 'icon.ico'),
      resolve(desktopRoot, 'assets', 'icon.ico'),
    ],
    window: process.platform === 'win32' ? [
      resolve(resourceRoot, 'assets', 'icon.ico'),
      resolve(desktopRoot, 'assets', 'icon.ico'),
      resolve(resourceRoot, 'assets', 'icon.png'),
      resolve(desktopRoot, 'assets', 'icon.png'),
    ] : [
      resolve(resourceRoot, 'assets', 'icon.png'),
      resolve(desktopRoot, 'assets', 'icon.png'),
      resolve(resourceRoot, 'assets', 'icon.ico'),
      resolve(desktopRoot, 'assets', 'icon.ico'),
    ],
  };
  const candidates = [
    ...(candidatesByKind[cacheKey] || candidatesByKind.window),
    resolve(clientDistRoot, 'assets', 'shine-logo.png'),
    resolve(repoRoot, 'client', 'assets', 'shine-logo-optimized.png'),
  ];
  const iconPath = candidates.find((candidate) => existsSync(candidate)) || '';
  cachedDesktopIconPaths.set(cacheKey, iconPath);
  return iconPath;
}

function getDesktopIconImage(kind = 'window', size = 256) {
  const iconPath = getDesktopIconPath(kind);
  if (!iconPath) return nativeImage.createEmpty();
  const cacheKey = `${kind}:${iconPath}`;
  let image = cachedDesktopIconImages.get(cacheKey);
  if (!image || image.isEmpty()) {
    image = nativeImage.createFromPath(iconPath);
    cachedDesktopIconImages.set(cacheKey, image);
  }
  if (!image || image.isEmpty()) return nativeImage.createEmpty();
  return size ? image.resize({ width: size, height: size }) : image;
}

async function writeDesktopDiagnosticsLine(message) {
  try {
    await mkdir(dirname(desktopDiagnosticsLogPath), { recursive: true });
    await writeFile(
      desktopDiagnosticsLogPath,
      `[${new Date().toISOString()}] ${message}\n`,
      { flag: 'a' },
    );
  } catch {
    // Diagnostics must never block app startup.
  }
}

function logDesktopIconDiagnostics() {
  void writeDesktopDiagnosticsLine([
    `mode=${desktopMode}`,
    `appVersion=${app.getVersion()}`,
    `appUserModelId=${APP_USER_MODEL_ID}`,
    `execPath=${process.execPath}`,
    `resourcesPath=${process.resourcesPath || ''}`,
    `windowIcon=${getDesktopIconPath('window')}`,
    `trayIcon=${getDesktopIconPath('tray')}`,
    `notificationIcon=${getDesktopIconPath('notification')}`,
  ].join(' | '));
}

function refreshWindowsShellIconCache() {
  if (process.platform !== 'win32' || !isPackagedDesktopApp) return;
  try {
    const result = spawnSync('ie4uinit.exe', ['-show'], {
      windowsHide: true,
      stdio: 'ignore',
      timeout: 3500,
    });
    void writeDesktopDiagnosticsLine(`shellIconCacheRefresh=ie4uinit -show | status=${result.status ?? 'unknown'} | signal=${result.signal || ''}`);
  } catch (error) {
    void writeDesktopDiagnosticsLine(`shellIconCacheRefreshFailed=${error instanceof Error ? error.message : 'unknown error'}`);
  }
}

function refreshWindowsShortcutIcons() {
  if (process.platform !== 'win32' || !isPackagedDesktopApp) return;
  const iconPath = getDesktopIconPath('window');
  if (!iconPath || !existsSync(iconPath)) return;
  const shortcutNames = [
    'RMKCET Shine.lnk',
    'RMKCET Shine Desktop.lnk',
    'rmkcet-shine-desktop.lnk',
    'rmkcet_shine_app.lnk',
  ];
  const shortcutRoots = [
    app.getPath('desktop'),
    resolve(app.getPath('appData'), 'Microsoft', 'Windows', 'Start Menu', 'Programs'),
    resolve(app.getPath('appData'), 'Microsoft', 'Windows', 'Start Menu', 'Programs', 'RMKCET Shine'),
    resolve(app.getPath('appData'), 'Microsoft', 'Internet Explorer', 'Quick Launch', 'User Pinned', 'TaskBar'),
    resolve(app.getPath('appData'), 'Microsoft', 'Internet Explorer', 'Quick Launch', 'User Pinned', 'StartMenu'),
  ];
  let refreshedCount = 0;
  for (const root of shortcutRoots) {
    for (const name of shortcutNames) {
      const shortcutPath = resolve(root, name);
      if (!existsSync(shortcutPath)) continue;
      try {
        shell.writeShortcutLink(shortcutPath, 'update', {
          target: process.execPath,
          cwd: dirname(process.execPath),
          description: 'RMKCET Shine',
          icon: iconPath,
          iconIndex: 0,
          appUserModelId: APP_USER_MODEL_ID,
        });
        refreshedCount += 1;
        void writeDesktopDiagnosticsLine(`shortcutIconRefreshed=${shortcutPath} | icon=${iconPath}`);
      } catch (error) {
        void writeDesktopDiagnosticsLine(`shortcutIconRefreshFailed=${shortcutPath} | ${error instanceof Error ? error.message : 'unknown error'}`);
      }
    }
  }
  if (refreshedCount > 0) refreshWindowsShellIconCache();
}

function restoreMainWindow() {
  if (!mainWindowRef || mainWindowRef.isDestroyed()) return;
  if (mainWindowRef.isMinimized()) mainWindowRef.restore();
  mainWindowRef.show();
  maximizeMainWindow();
  mainWindowRef.focus();
}

function showDesktopNotification(payload = {}) {
  if (!desktopSettings.desktopNotificationsEnabled || !Notification.isSupported()) return false;
  const title = String(payload.title || 'RMKCET Shine').trim();
  const body = String(payload.body || payload.message || '').trim();
  const notification = new Notification({
    title,
    body,
    icon: getDesktopIconPath('notification') || getDesktopIconImage('notification', 256),
    silent: Boolean(payload.silent),
  });
  notification.on('click', restoreMainWindow);
  notification.show();
  return true;
}

function updateTrayMenu() {
  if (!appTray) return;
  appTray.setToolTip('RMKCET Shine');
  appTray.setContextMenu(Menu.buildFromTemplate([
    { label: 'Open Shine', click: restoreMainWindow },
    { label: 'Desktop Settings', click: () => openDesktopSettings() },
    { label: 'Check Updates', click: () => void checkDesktopUpdate({ interactive: true }) },
    { type: 'separator' },
    {
      label: 'Quit',
      click: () => {
        appIsQuitting = true;
        app.quit();
      },
    },
  ]));
}

function createTray() {
  if (appTray) return appTray;
  const trayIconPath = getDesktopIconPath('tray');
  appTray = new Tray(process.platform === 'win32' && trayIconPath ? trayIconPath : getDesktopIconImage('tray', 16));
  appTray.on('click', restoreMainWindow);
  updateTrayMenu();
  return appTray;
}

function scheduleDesktopUpdateChecks() {
  if (!isPackagedDesktopApp || desktopMode !== 'desktop-app' || desktopUpdateCheckTimer) return;
  const intervalMinutes = Math.max(10, Math.min(120, Number(desktopSettings.notificationPollMinutes || 30) || 30));
  desktopUpdateCheckTimer = setInterval(() => {
    if (!desktopSettings.updateChecksEnabled || updateInstallInProgress) return;
    void checkDesktopUpdate({ quiet: true });
  }, intervalMinutes * 60 * 1000);
}

function openDesktopSettings() {
  restoreMainWindow();
  if (mainWindowRef && !mainWindowRef.isDestroyed()) {
    mainWindowRef.webContents.send('shine:desktopSettings:open');
  }
}

function buildNoInternetHtml(state = lastConnectivityState) {
  const message = escapeHtml(state.error || 'Server is unreachable.');
  return `<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>RMKCET Shine - Recovery</title>
  <style>
    :root{font-family:Inter,Segoe UI,system-ui,sans-serif;color:#0f172a;background:#f4f7fb}
    *{box-sizing:border-box}body{margin:0;min-height:100vh;display:grid;place-items:center;padding:28px;background:radial-gradient(circle at top left,rgba(102,126,234,.16),transparent 34%),#f4f7fb}
    main{width:min(820px,100%);background:#fff;border:1px solid rgba(148,163,184,.35);border-radius:18px;box-shadow:0 24px 70px rgba(15,23,42,.16);padding:28px}
    h1{margin:0 0 8px;font-size:1.45rem}p{margin:0 0 18px;color:#475569;line-height:1.55}.actions{display:flex;flex-wrap:wrap;gap:10px;margin:18px 0 0}.btn{border:1px solid #cbd5e1;background:#fff;color:#0f172a;border-radius:10px;padding:10px 14px;font-weight:700;cursor:pointer}.btn.primary{border-color:#667eea;background:linear-gradient(135deg,#667eea,#764ba2);color:#fff}
  </style>
</head>
<body>
  <main>
    <h1>Server is unreachable</h1>
    <p>${message}</p>
    <div class="actions">
      <button class="btn primary" id="retry">Retry</button>
    </div>
  </main>
  <script>
    document.getElementById('retry').addEventListener('click', () => window.__SHINE_DESKTOP__?.retryDesktopConnectivity?.());
  </script>
</body>
</html>`;
}

async function showNoInternetPage() {
  if (!mainWindowRef || mainWindowRef.isDestroyed()) return;
  await mainWindowRef.loadURL(`data:text/html;charset=utf-8,${encodeURIComponent(buildNoInternetHtml())}`);
}

function buildStartupUpdateHtml(state = {}) {
  const title = escapeHtml(state.title || 'Preparing RMKCET Shine');
  const message = escapeHtml(state.message || 'Checking for the latest desktop update before opening the app.');
  const detail = escapeHtml(state.detail || '');
  const phase = escapeHtml(state.phase || 'Update check');
  const progress = Number.isFinite(Number(state.progress))
    ? Math.max(0, Math.min(100, Math.round(Number(state.progress))))
    : null;
  const progressLabel = progress === null ? 'Working...' : `${progress}%`;
  const progressStyle = progress === null
    ? 'width:42%;animation:move 1.25s ease-in-out infinite'
    : `width:${progress}%`;
  return `<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>RMKCET Shine - Updating</title>
  <style>
    :root{font-family:Inter,Segoe UI,system-ui,sans-serif;color:#172033;background:#eef3f8}
    *{box-sizing:border-box}body{margin:0;min-height:100vh;display:grid;place-items:center;padding:32px;background:linear-gradient(180deg,#f7fafc,#e9f0f7)}
    main{width:min(760px,100%);border:1px solid #d7e0ea;border-radius:18px;padding:30px;background:#fff;box-shadow:0 22px 70px rgba(15,23,42,.14)}
    .top{display:flex;align-items:center;gap:16px;margin-bottom:22px}.mark{width:54px;height:54px;border-radius:14px;display:grid;place-items:center;background:#0f766e;color:#fff;font-size:28px;font-weight:900;box-shadow:0 14px 26px rgba(15,118,110,.18)}
    .brand{font-size:.78rem;text-transform:uppercase;letter-spacing:.08em;color:#64748b;font-weight:800}.phase{margin-top:3px;font-size:.82rem;color:#0f766e;font-weight:800}
    h1{margin:0 0 10px;font-size:1.55rem;letter-spacing:0;color:#111827}p{margin:0;color:#526173;line-height:1.6}.detail{margin-top:18px;padding:13px 15px;border-radius:12px;background:#f8fafc;border:1px solid #e2e8f0;color:#334155;font-size:.9rem}
    .meter{margin-top:24px}.bar{height:10px;border-radius:999px;overflow:hidden;background:#e2e8f0}.fill{display:block;height:100%;border-radius:inherit;background:linear-gradient(90deg,#0f766e,#f59e0b);${progressStyle}}
    .meta{display:flex;justify-content:space-between;gap:12px;margin-top:10px;color:#64748b;font-size:.78rem;font-weight:700}
    @keyframes move{0%{transform:translateX(-110%)}100%{transform:translateX(250%)}}
  </style>
</head>
<body>
  <main>
    <div class="top">
      <div class="mark">S</div>
      <div>
        <div class="brand">RMKCET Shine Desktop</div>
        <div class="phase">${phase}</div>
      </div>
    </div>
    <h1>${title}</h1>
    <p>${message}</p>
    ${detail ? `<div class="detail">${detail}</div>` : ''}
    <div class="meter">
      <div class="bar"><span class="fill"></span></div>
      <div class="meta"><span>Please keep Shine open</span><span>${progressLabel}</span></div>
    </div>
  </main>
</body>
</html>`;
}

async function showStartupUpdatePage(state = {}) {
  if (!mainWindowRef || mainWindowRef.isDestroyed()) return;
  await writeFile(desktopUpdateStatusHtmlPath, buildStartupUpdateHtml(state), 'utf8');
  await mainWindowRef.loadFile(desktopUpdateStatusHtmlPath);
  mainWindowRef.show();
  maximizeMainWindow();
}

function compareVersions(left, right) {
  const leftParts = String(left || '0.0.0').split(/[.-]/).map((part) => Number.parseInt(part, 10) || 0);
  const rightParts = String(right || '0.0.0').split(/[.-]/).map((part) => Number.parseInt(part, 10) || 0);
  const length = Math.max(leftParts.length, rightParts.length);
  for (let index = 0; index < length; index += 1) {
    const diff = (leftParts[index] || 0) - (rightParts[index] || 0);
    if (diff !== 0) return diff;
  }
  return 0;
}

function buildManifestUrl(baseUrl) {
  const raw = String(baseUrl || '').trim().replace(/\/+$/, '');
  if (!raw) return '';
  if (/\/meta$/i.test(raw)) return raw;
  if (/\/api\/desktop\/installer$/i.test(raw)) return `${raw}/meta`;
  if (/release\.json$/i.test(raw)) return raw;
  return `${raw}/api/desktop/installer/meta`;
}

function buildUpdaterFeedUrl(baseUrl) {
  const raw = String(baseUrl || '').trim().replace(/\/+$/, '');
  if (!raw) return '';
  if (/\/latest\.ya?ml$/i.test(raw)) return raw.replace(/\/latest\.ya?ml$/i, '');
  if (/\/api\/desktop\/updater$/i.test(raw)) return raw;
  if (/\/api\/desktop\/installer\/meta$/i.test(raw)) return raw.replace(/\/api\/desktop\/installer\/meta$/i, '/api/desktop/updater');
  if (/\/api\/desktop\/installer$/i.test(raw)) return raw.replace(/\/api\/desktop\/installer$/i, '/api/desktop/updater');
  return `${raw}/api/desktop/updater`;
}

function getDesktopUpdaterFeedUrl() {
  return buildUpdaterFeedUrl(getReleaseChannelBaseUrl());
}

const desktopUpdaterLogger = {
  info(message) {
    console.log(`[desktop-updater] ${message}`);
  },
  warn(message) {
    console.warn(`[desktop-updater] ${message}`);
  },
  error(message) {
    console.error(`[desktop-updater] ${message}`);
  },
  debug(message) {
    if (process.env.SHINE_DESKTOP_UPDATE_DEBUG === '1') console.log(`[desktop-updater] ${message}`);
  },
};

let desktopUpdaterConfiguredFor = '';
let desktopUpdaterEventsAttached = false;

function attachDesktopUpdaterEvents() {
  if (desktopUpdaterEventsAttached) return;
  desktopUpdaterEventsAttached = true;
  autoUpdater.on('download-progress', (progress = {}) => {
    if (!updateInstallInProgress) return;
    const percent = Number(progress.percent || 0);
    const transferredMb = Math.round(Number(progress.transferred || 0) / 1024 / 1024);
    const totalMb = Math.round(Number(progress.total || 0) / 1024 / 1024);
    void showStartupUpdatePage({
      phase: 'Downloading update',
      title: `Downloading Shine ${pendingUpdateInfo?.version || 'update'}`,
      message: 'The desktop app is downloading the latest installer from the release channel.',
      detail: totalMb > 0 ? `${transferredMb} MB of ${totalMb} MB` : getDesktopUpdaterFeedUrl(),
      progress: Number.isFinite(percent) ? percent : 0,
    });
  });
  autoUpdater.on('update-downloaded', () => {
    if (!updateInstallInProgress) return;
    void showStartupUpdatePage({
      phase: 'Installing update',
      title: `Installing Shine ${pendingUpdateInfo?.version || 'update'}`,
      message: 'Shine will launch the updater and reopen automatically.',
      detail: 'Windows may ask for administrator permission to complete the update.',
      progress: 100,
    });
  });
  autoUpdater.on('error', (error) => {
    desktopUpdaterLogger.error(error instanceof Error ? error.message : String(error));
  });
}

function configureDesktopUpdater() {
  if (!isPackagedDesktopApp || desktopMode !== 'desktop-app') return '';
  const feedUrl = getDesktopUpdaterFeedUrl();
  if (!/^https?:\/\//i.test(feedUrl)) return '';
  if (desktopUpdaterConfiguredFor === feedUrl) return feedUrl;
  autoUpdater.logger = desktopUpdaterLogger;
  autoUpdater.autoDownload = false;
  autoUpdater.autoInstallOnAppQuit = false;
  autoUpdater.allowDowngrade = false;
  autoUpdater.disableWebInstaller = true;
  autoUpdater.setFeedURL({
    provider: 'generic',
    url: feedUrl,
  });
  attachDesktopUpdaterEvents();
  desktopUpdaterConfiguredFor = feedUrl;
  return feedUrl;
}

function quoteCmdArg(value) {
  return `"${String(value || '').replace(/"/g, '""')}"`;
}

function quotePowerShellSingle(value) {
  return `'${String(value || '').replace(/'/g, "''")}'`;
}

function buildWindowsUpdateHandoffCommand({ installerPath, appPath, logPath }) {
  const installer = quoteCmdArg(installerPath);
  const appExe = quoteCmdArg(appPath);
  const logFile = quoteCmdArg(logPath);
  const installerPs = quotePowerShellSingle(installerPath);
  const logFilePs = quotePowerShellSingle(logPath);
  const elevatedInstallCommand = [
    "$ErrorActionPreference = 'Stop'",
    `$p = Start-Process -FilePath ${installerPs} -ArgumentList @('/S','/currentuser') -Verb RunAs -Wait -PassThru`,
    `$code = if ($null -ne $p) { $p.ExitCode } else { -9999 }`,
    `Add-Content -LiteralPath ${logFilePs} -Value "[$(Get-Date -Format 'yyyy-MM-dd HH:mm:ss')] Elevated installer exit code: $code"`,
    'exit $code',
  ].join('; ');
  return [
    'set "SEE_MASK_NOZONECHECKS=1"',
    `echo [%date% %time%] Starting Shine updater handoff > ${logFile}`,
    `echo [%date% %time%] Installer: ${installer} >> ${logFile}`,
    `echo [%date% %time%] App: ${appExe} >> ${logFile}`,
    `if not exist ${installer} (echo [%date% %time%] Installer file is missing. >> ${logFile} & if exist ${appExe} start "" ${appExe} & exit /b 2)`,
    'timeout /t 2 /nobreak >nul',
    `echo [%date% %time%] Requesting administrator rights for installer. >> ${logFile}`,
    `powershell.exe -NoProfile -Command ${quoteCmdArg(elevatedInstallCommand)} >> ${logFile} 2>&1`,
    'set "SHINE_INSTALL_EXIT=!ERRORLEVEL!"',
    `echo [%date% %time%] Installer exit code: !SHINE_INSTALL_EXIT! >> ${logFile}`,
    'timeout /t 2 /nobreak >nul',
    `if exist ${appExe} (echo [%date% %time%] Relaunching Shine. >> ${logFile} & start "" ${appExe}) else (echo [%date% %time%] App path missing after install; cannot relaunch. >> ${logFile})`,
    'exit /b !SHINE_INSTALL_EXIT!',
  ].join(' & ');
}

function getUpdateInstallerFileName(updateInfo) {
  return String(updateInfo?.manifest?.files?.exe?.fileName || `RMKCET-Shine-Setup-${updateInfo?.version || 'latest'}.exe`).replace(/[\\/:*?"<>|]+/g, '-');
}

function getUpdateInstallerCachePaths(updateInfo) {
  const targetDir = resolve(desktopUpdateRoot, String(updateInfo?.version || 'latest'));
  const installerPath = resolve(targetDir, getUpdateInstallerFileName(updateInfo));
  return {
    targetDir,
    installerPath,
    metadataPath: resolve(targetDir, 'installer-cache.json'),
    logPath: resolve(targetDir, 'install.log'),
  };
}

function getExpectedInstallerSize(updateInfo) {
  const raw = Number(updateInfo?.manifest?.files?.exe?.size || updateInfo?.manifest?.files?.exe?.bytes || 0);
  return Number.isFinite(raw) && raw > 0 ? raw : 0;
}

function getExpectedInstallerSha256(updateInfo) {
  return String(updateInfo?.manifest?.files?.exe?.sha256 || updateInfo?.manifest?.files?.exe?.hash || '').trim().toLowerCase();
}

async function hashLocalFileSha256(filePath) {
  return new Promise((resolvePromise, rejectPromise) => {
    const hash = createHash('sha256');
    const stream = createReadStream(filePath);
    stream.on('data', (chunk) => hash.update(chunk));
    stream.on('error', rejectPromise);
    stream.on('end', () => resolvePromise(hash.digest('hex')));
  });
}

async function readCachedInstallerMetadata(metadataPath) {
  try {
    return JSON.parse(await readFile(metadataPath, 'utf8'));
  } catch {
    return null;
  }
}

async function validateCachedInstaller(updateInfo, paths) {
  const details = await stat(paths.installerPath).catch(() => null);
  if (!details?.isFile?.() || details.size <= 0) return { valid: false, reason: 'missing' };

  const expectedSize = getExpectedInstallerSize(updateInfo);
  if (expectedSize > 0 && details.size !== expectedSize) {
    return { valid: false, reason: `size mismatch (${details.size}/${expectedSize})` };
  }

  const expectedSha256 = getExpectedInstallerSha256(updateInfo);
  if (expectedSha256) {
    const actualSha256 = await hashLocalFileSha256(paths.installerPath);
    if (actualSha256 !== expectedSha256) return { valid: false, reason: 'sha256 mismatch' };
    return { valid: true, reason: 'sha256 match', size: details.size, sha256: actualSha256 };
  }
  if (expectedSize > 0) return { valid: true, reason: 'size match', size: details.size };

  const metadata = await readCachedInstallerMetadata(paths.metadataPath);
  const metadataMatches = metadata
    && String(metadata.version || '') === String(updateInfo?.version || '')
    && String(metadata.exeUrl || '') === String(updateInfo?.exeUrl || '')
    && Number(metadata.size || 0) === details.size;
  return metadataMatches
    ? { valid: true, reason: 'metadata match', size: details.size }
    : { valid: false, reason: 'no trusted cache metadata' };
}

async function writeCachedInstallerMetadata(updateInfo, paths, size, sha256 = '') {
  await writeFile(paths.metadataPath, JSON.stringify({
    version: String(updateInfo?.version || ''),
    exeUrl: String(updateInfo?.exeUrl || ''),
    fileName: getUpdateInstallerFileName(updateInfo),
    size,
    sha256,
    cachedAt: new Date().toISOString(),
  }, null, 2), 'utf8');
}

async function checkDesktopUpdate(options = {}) {
  if (!desktopSettings.updateChecksEnabled && !options.interactive && !options.force) {
    return { available: false, skipped: true, reason: 'Update checks are disabled.' };
  }
  const feedUrl = configureDesktopUpdater();
  const manifestUrl = feedUrl ? `${feedUrl}/latest.yml` : buildManifestUrl(getReleaseChannelBaseUrl());
  const currentVersion = String(app.getVersion() || process.env.SHINE_DESKTOP_APP_VERSION || '0.1.0').trim();
  if (!feedUrl) {
    return {
      available: false,
      currentVersion,
      error: isPackagedDesktopApp ? 'Desktop updater feed is not configured.' : 'Update checks run only in the packaged desktop app.',
      manifestUrl,
    };
  }
  try {
    const result = await autoUpdater.checkForUpdates();
    const updateInfo = result?.updateInfo || null;
    const latestVersion = String(updateInfo?.version || currentVersion).trim();
    const available = Boolean(latestVersion && compareVersions(latestVersion, currentVersion) > 0);
    const info = {
      available,
      currentVersion,
      version: latestVersion || currentVersion,
      manifestUrl,
      exeUrl: '',
      releaseNotes: Array.isArray(updateInfo?.releaseNotes) ? updateInfo.releaseNotes : [],
      manifest: updateInfo,
    };
    pendingUpdateInfo = available ? info : null;
    if (available) {
      if (!options.quiet) {
        showDesktopNotification({ title: 'Shine update available', body: `Version ${latestVersion} is ready to install.` });
      }
      if (options.install) {
        const installResult = await installDesktopUpdate(info);
        return { ...info, installing: installResult.success, installResult };
      }
      if (desktopSettings.autoInstallUpdatesWhenIdle && !desktopWorkspaceActive && !floatingSendWindow) {
        void promptAndInstallDesktopUpdate(info);
      }
    } else if (options.interactive) {
      dialog.showMessageBox(mainWindowRef || undefined, {
        type: 'info',
        title: 'Shine Updates',
        message: 'Shine is up to date.',
        detail: `Installed version: ${currentVersion}`,
      });
    }
    return info;
  } catch (error) {
    const result = {
      available: false,
      error: error instanceof Error ? error.message : 'Update check failed.',
      manifestUrl,
    };
    if (options.interactive) {
      dialog.showMessageBox(mainWindowRef || undefined, {
        type: 'error',
        title: 'Update check failed',
        message: result.error,
      });
    }
    return result;
  }
}

async function installDesktopUpdate(updateInfo = pendingUpdateInfo) {
  const targetUpdateInfo = updateInfo?.available ? updateInfo : await checkDesktopUpdate({ force: true, quiet: true });
  if (!targetUpdateInfo?.available) {
    return { success: false, error: targetUpdateInfo?.error || 'No desktop update is available.' };
  }
  if (desktopWorkspaceActive || floatingSendWindow) {
    pendingUpdateInfo = targetUpdateInfo;
    return { success: false, deferred: true, error: 'A send workflow is active. The update will wait until it closes.' };
  }
  if (updateInstallInProgress) return { success: false, error: 'Update install is already running.' };
  if (!configureDesktopUpdater()) return { success: false, error: 'Desktop updater feed is not configured.' };
  updateInstallInProgress = true;
  pendingUpdateInfo = targetUpdateInfo;
  try {
    showDesktopNotification({ title: 'Downloading Shine update', body: `Version ${targetUpdateInfo.version} is downloading.` });
    await showStartupUpdatePage({
      phase: 'Downloading update',
      title: `Downloading Shine ${targetUpdateInfo.version}`,
      message: 'The desktop app is downloading the latest installer from the release channel.',
      detail: targetUpdateInfo.manifestUrl || getDesktopUpdaterFeedUrl(),
      progress: 0,
    });
    await autoUpdater.downloadUpdate();
    await showStartupUpdatePage({
      phase: 'Installing update',
      title: `Installing Shine ${targetUpdateInfo.version}`,
      message: 'Shine will launch the signed NSIS updater and reopen automatically.',
      detail: 'Windows may ask for administrator permission to complete the update.',
      progress: 100,
    });
    showDesktopNotification({ title: 'Installing Shine update', body: 'The installer is starting now.' });
    appIsQuitting = true;
    autoUpdater.quitAndInstall(true, true);
    return { success: true };
  } catch (error) {
    updateInstallInProgress = false;
    const message = error instanceof Error ? error.message : 'Update install failed.';
    showDesktopNotification({ title: 'Shine update failed', body: message });
    return { success: false, error: message };
  }
}

async function runStartupUpdateGate() {
  if (!isPackagedDesktopApp || desktopMode !== 'desktop-app') {
    return { checked: false, reason: 'Startup update gate is only for packaged desktop app mode.' };
  }
  if (!lastConnectivityState.online) {
    return { checked: false, reason: 'Server is offline.' };
  }

  await showStartupUpdatePage({
    title: 'Checking for Shine updates',
    message: 'The desktop app is contacting the release channel before opening.',
    detail: `Server: ${apiOrigin}`,
  });

  let lastResult = null;
  for (let attempt = 1; attempt <= 3; attempt += 1) {
    await showStartupUpdatePage({
      title: 'Checking for Shine updates',
      message: `Looking for the latest desktop package. Attempt ${attempt} of 3.`,
      detail: `Release channel: ${getReleaseChannelBaseUrl()}`,
    });
    lastResult = await checkDesktopUpdate({ force: true, quiet: true, install: true });
    if (lastResult?.installing) {
      await showStartupUpdatePage({
        title: 'Installing Shine update',
        message: `Version ${lastResult.version} is downloading and installing. Shine will restart automatically.`,
        detail: 'Please do not close this window.',
      });
      return { checked: true, installing: true, result: lastResult };
    }
    if (!lastResult?.error) {
      await showStartupUpdatePage({
        title: 'Shine is up to date',
        message: 'Opening the desktop app now.',
        detail: `Installed version: ${lastResult?.currentVersion || app.getVersion()}`,
      });
      await delay(650);
      return { checked: true, updated: false, result: lastResult };
    }
    await delay(900);
  }

  await showStartupUpdatePage({
    title: 'Update check could not complete',
    message: 'Shine will open with the installed version. You can check updates again from the tray menu.',
    detail: lastResult?.error || 'Unknown update check failure.',
  });
  await delay(1600);
  return { checked: true, updated: false, error: lastResult?.error || 'Update check failed.' };
}

async function promptAndInstallDesktopUpdate(updateInfo) {
  if (!updateInfo?.available || desktopWorkspaceActive || floatingSendWindow) return;
  const result = await dialog.showMessageBox(mainWindowRef || undefined, {
    type: 'info',
    buttons: ['Install Now', 'Later'],
    defaultId: 0,
    cancelId: 1,
    title: 'Shine update available',
    message: `Shine ${updateInfo.version} is available.`,
    detail: 'The app will download the installer, launch it, and close this window.',
  });
  if (result.response === 0) {
    await installDesktopUpdate(updateInfo);
  }
}

function getFloatingSendBounds() {
  const display = screen.getPrimaryDisplay();
  const area = display.workArea || display.bounds;
  return {
    x: area.x + 18,
    y: area.y + 18,
    width: 380,
    height: Math.min(560, Math.max(440, area.height - 160)),
  };
}

function normalizeFloatingSendPayload(payload) {
  const rawThemeVars = payload?.themeVars && typeof payload.themeVars === 'object' ? payload.themeVars : {};
  return {
    kind: payload?.kind === 'notice' ? 'notice' : 'report',
    mode: payload?.mode === 'web' ? 'web' : payload?.mode === 'embed' ? 'embed' : 'app',
    title: String(payload?.title || 'Student Send List'),
    subtitle: String(payload?.subtitle || ''),
    theme: payload?.theme === 'dark' ? 'dark' : 'light',
    themeVars: Object.fromEntries(
      Object.entries(rawThemeVars)
        .map(([key, value]) => [key, String(value || '').trim()])
        .filter(([, value]) => /^#(?:[0-9a-f]{3}|[0-9a-f]{6}|[0-9a-f]{8})$/i.test(value) || /^rgba?\(/i.test(value)),
    ),
    rows: Array.isArray(payload?.rows) ? payload.rows.map((row) => ({
      regNo: String(row?.regNo || ''),
      studentName: String(row?.studentName || ''),
      parentPhone: String(row?.parentPhone || ''),
      status: String(row?.status || ''),
      queueState: String(row?.queueState || ''),
      active: Boolean(row?.active),
      loading: Boolean(row?.loading),
    })).filter((row) => row.regNo) : [],
  };
}

function buildFloatingSendHtml() {
  return `<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <meta http-equiv="Content-Security-Policy" content="default-src 'self' data:; script-src 'unsafe-inline'; style-src 'unsafe-inline';">
  <title>Shine Student Send List</title>
  <style>
    :root{color-scheme:dark;font-family:Inter,system-ui,-apple-system,Segoe UI,sans-serif;--bg-primary:#0a0c14;--bg-secondary:#0f1219;--bg-card:rgba(20,30,50,.65);--bg-input:rgba(15,20,35,.8);--border:rgba(102,126,234,.18);--border-light:rgba(255,255,255,.06);--primary:#667eea;--secondary:#764ba2;--success:#25D366;--text:#e2e8f0;--text-strong:#f8fafc;--text-dim:#94a3b8;--radius:12px;--radius-sm:8px;--transition:.25s ease}
    body.light-theme{color-scheme:light;--bg-primary:#f5f7fb;--bg-secondary:#ffffff;--bg-card:rgba(255,255,255,.95);--bg-input:#ffffff;--border:rgba(148,163,184,.35);--border-light:rgba(148,163,184,.22);--text:#0f172a;--text-strong:#020617;--text-dim:#334155}
    *{box-sizing:border-box}body{margin:0;min-height:100vh;background:var(--bg-primary);color:var(--text);overflow:hidden}
    .shell{height:100vh;background:linear-gradient(180deg,#111827 0%,#0f1219 100%);display:flex;flex-direction:column;border-right:1px solid var(--border)}
    body.light-theme .shell{background:linear-gradient(180deg,#ffffff 0%,#eef3fb 100%)}
    header{display:flex;align-items:center;gap:8px;padding:12px;border-bottom:1px solid var(--border);background:color-mix(in srgb,var(--bg-secondary) 96%,transparent);-webkit-app-region:drag}
    button{-webkit-app-region:no-drag;font-family:inherit}
    .icon-btn{width:34px;height:34px;display:inline-flex;align-items:center;justify-content:center;gap:7px;padding:6px 10px;border-radius:var(--radius-sm);background:transparent;color:var(--text-dim);border:1px solid var(--border);cursor:pointer;font-size:.8rem;font-weight:600;line-height:1;transition:all var(--transition);text-decoration:none}
    .icon-btn:hover{border-color:var(--primary);color:var(--text-strong);box-shadow:0 6px 20px rgba(102,126,234,.18);transform:translateY(-1px)}
    body.light-theme .icon-btn:hover{color:#0f172a}
    .icon-btn svg{width:14px;height:14px;display:block}
    .title{min-width:0;flex:1}.title strong{display:block;font-size:14px;color:var(--text-strong);white-space:nowrap;overflow:hidden;text-overflow:ellipsis}.title span{display:block;margin-top:3px;color:var(--text-dim);font-size:12px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
    .panel{margin:8px;padding:8px 8px 6px;display:flex;flex:1;min-height:0;flex-direction:column;gap:6px;border:1px solid rgba(102,126,234,.22);border-radius:var(--radius);background:color-mix(in srgb,var(--bg-card) 88%,rgba(102,126,234,.08));box-shadow:0 10px 28px rgba(15,23,42,.08)}
    .list{flex:1;min-height:0;overflow-y:auto;display:flex;flex-direction:column;gap:4px;overflow-anchor:none;scroll-behavior:auto}
    .student{display:grid;grid-template-columns:minmax(0,1fr) 156px;align-items:center;gap:10px;padding:10px;border:1px solid var(--border);border-radius:var(--radius-sm);background:var(--bg-input)}
    .student.active{border-color:rgba(37,211,102,.45);background:rgba(37,211,102,.10)}
    .student.generated{opacity:.9}.student-main{min-width:0;display:flex;align-items:center}.student-main strong{display:block;font-size:.88rem;font-weight:600;color:var(--text);line-height:1.2;white-space:nowrap;overflow:hidden;text-overflow:ellipsis;letter-spacing:0}
    .send-btn{width:100%;min-height:28px;display:inline-flex;align-items:center;justify-content:center;gap:7px;padding:6px 14px;border:none;border-radius:var(--radius-sm);background:linear-gradient(135deg,var(--primary),var(--secondary));color:#fff;font-size:.8rem;font-weight:600;cursor:pointer;transition:all var(--transition);white-space:nowrap}
    .send-btn:hover:not(:disabled){box-shadow:0 6px 20px rgba(102,126,234,.4);transform:translateY(-1px);color:#fff}
    .send-btn.generated{background:rgba(100,116,139,.18)!important;border:1px solid rgba(100,116,139,.32)!important;color:var(--text-dim)!important;box-shadow:none!important}
    body.light-theme .send-btn.generated{background:rgba(100,116,139,.18)!important;border-color:rgba(100,116,139,.32)!important;color:var(--text-dim)!important}
    .send-btn svg{width:13px;height:13px;flex:0 0 auto;display:block}
    .send-btn:disabled{opacity:.74;cursor:wait;transform:none;box-shadow:none}
    .empty{color:var(--text-dim);text-align:center;padding:28px 10px;font-size:13px}
  </style>
</head>
<body>
  <main class="shell">
    <header>
      <button class="icon-btn back" type="button" title="Back" aria-label="Back">
        <svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M15.5 19.5 8 12l7.5-7.5 1.4 1.4L10.8 12l6.1 6.1-1.4 1.4Z"/></svg>
      </button>
      <div class="title"><strong id="floatingTitle">Student Send List</strong><span id="floatingSubtitle">0 students</span></div>
      <button class="icon-btn theme" type="button" title="Toggle theme" id="themeButton" aria-label="Toggle theme"></button>
      <button class="icon-btn close" type="button" title="Close" aria-label="Close">
        <svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="m12 10.6 4.95-4.95 1.4 1.4L13.4 12l4.95 4.95-1.4 1.4L12 13.4l-4.95 4.95-1.4-1.4L10.6 12 5.65 7.05l1.4-1.4L12 10.6Z"/></svg>
      </button>
    </header>
    <section class="panel"><div class="list" id="floatingList"><div class="empty">Loading students...</div></div></section>
  </main>
  <script>
    const list = document.getElementById('floatingList');
    const title = document.getElementById('floatingTitle');
    const subtitle = document.getElementById('floatingSubtitle');
    const themeButton = document.getElementById('themeButton');
    let desiredScrollTop = 0;
    const rowNodes = new Map();
    const setText = (element, value) => { element.textContent = String(value || ''); };
    const themeVarMap = {
      primary: '--primary',
      primaryDark: '--primary-d',
      secondary: '--secondary',
      accent: '--accent',
      success: '--success',
      warning: '--warning',
      danger: '--danger',
      info: '--info',
      bgPrimary: '--bg-primary',
      bgSecondary: '--bg-secondary',
      bgCard: '--bg-card',
      text: '--text',
      textDim: '--text-dim',
      textMuted: '--text-muted',
      border: '--border',
    };
    function applyThemeVars(vars) {
      const root = document.documentElement;
      for (const [key, cssName] of Object.entries(themeVarMap)) {
        const value = vars && vars[key];
        if (value) root.style.setProperty(cssName, value);
      }
    }
    const whatsappIcon = '<svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M12.04 2a9.86 9.86 0 0 0-8.52 14.83L2.5 22l5.32-1a9.95 9.95 0 1 0 4.22-19Zm0 1.8a8.15 8.15 0 1 1-4.03 15.23l-.3-.17-3.05.58.58-2.97-.2-.31A8.15 8.15 0 0 1 12.04 3.8Zm-3.2 4.33c-.18 0-.46.07-.7.34-.24.26-.92.9-.92 2.2s.94 2.55 1.07 2.72c.13.18 1.84 2.95 4.55 4.02 2.25.88 2.71.7 3.2.66.49-.04 1.58-.64 1.8-1.26.22-.62.22-1.15.15-1.26-.07-.11-.24-.18-.51-.31-.27-.13-1.58-.78-1.82-.87-.24-.09-.42-.13-.6.13-.18.27-.69.87-.84 1.04-.15.18-.31.2-.58.07-.27-.13-1.14-.42-2.17-1.34-.8-.72-1.35-1.6-1.51-1.87-.16-.27-.02-.42.12-.55.12-.12.27-.31.4-.47.13-.16.18-.27.27-.45.09-.18.04-.34-.02-.47-.07-.13-.6-1.43-.82-1.96-.22-.52-.44-.45-.6-.46h-.51Z"/></svg>';
    function setButtonLabel(button, text) {
      button.innerHTML = whatsappIcon + '<span>' + String(text || '') + '</span>';
    }
    function setManagedScrollTop(top) {
      desiredScrollTop = Math.max(0, Number(top) || 0);
      list.scrollTop = desiredScrollTop;
    }
    function restoreManagedScroll() {
      list.scrollTop = desiredScrollTop;
    }
    function resetManagedScroll() {
      setManagedScrollTop(0);
    }
    function getRowStep(rowElement) {
      const next = rowElement?.nextElementSibling;
      if (next) return Math.max(1, next.offsetTop - rowElement.offsetTop);
      const rect = rowElement?.getBoundingClientRect();
      return Math.max(1, Math.round(rect?.height || 0) + 4);
    }
    function clampScrollTop(top) {
      return Math.min(Math.max(0, Number(top) || 0), Math.max(0, list.scrollHeight - list.clientHeight));
    }
    function scrollDownOneStudent(rowElement) {
      const top = clampScrollTop(desiredScrollTop + getRowStep(rowElement));
      setManagedScrollTop(top);
    }
    list.addEventListener('scroll', () => {
      desiredScrollTop = list.scrollTop;
    }, { passive: true });
    function isFinished(row) {
      return row.status === 'Generated' || row.queueState === 'sent';
    }
    function setTheme(theme) {
      const light = theme === 'light';
      document.body.classList.toggle('light-theme', light);
      themeButton.innerHTML = light
        ? '<svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M20.4 14.5A8 8 0 0 1 9.5 3.6 8.5 8.5 0 1 0 20.4 14.5Z"/></svg>'
        : '<svg viewBox="0 0 24 24" aria-hidden="true"><path fill="currentColor" d="M12 18a6 6 0 1 1 0-12 6 6 0 0 1 0 12Zm0-2a4 4 0 1 0 0-8 4 4 0 0 0 0 8ZM11 1h2v3h-2V1Zm0 19h2v3h-2v-3ZM1 11h3v2H1v-2Zm19 0h3v2h-3v-2ZM4.22 2.8 6.34 4.93 4.93 6.34 2.8 4.22 4.22 2.8Zm14.85 14.86 2.12 2.12-1.41 1.41-2.12-2.12 1.41-1.41Zm.7-14.86 1.42 1.42-2.12 2.12-1.41-1.41 2.12-2.13ZM4.93 17.66l1.41 1.41-2.12 2.12-1.42-1.41 2.13-2.12Z"/></svg>';
    }
    function makeRow(row) {
      const item = document.createElement('article');
      const main = document.createElement('div');
      main.className = 'student-main';
      const name = document.createElement('strong');
      const button = document.createElement('button');
      button.type = 'button';
      button.className = 'send-btn';
      button.addEventListener('click', () => {
        const regNo = button.dataset.reg || '';
        button.disabled = true;
        setButtonLabel(button, 'Opening...');
        item.classList.add('active');
        scrollDownOneStudent(item);
        requestAnimationFrame(restoreManagedScroll);
        setTimeout(() => restoreManagedScroll(), 120);
        window.__SHINE_DESKTOP__?.pickFloatingSendStudent?.(regNo);
      });
      main.append(name);
      item.append(main, button);
      return { item, name, button };
    }
    function patchRow(node, row) {
      const generated = isFinished(row);
      node.item.className = 'student' + (generated ? ' generated' : '') + (row.active ? ' active' : '');
      setText(node.name, row.studentName || row.regNo || '');
      node.button.dataset.reg = row.regNo || '';
      node.button.disabled = Boolean(row.loading);
      node.button.className = 'send-btn' + (generated ? ' generated' : '');
      setButtonLabel(node.button, row.loading ? 'Opening...' : 'Send To WhatsApp');
      return node.item;
    }
    function render(payload) {
      const rows = Array.isArray(payload?.rows) ? payload.rows : [];
      const shouldResetScroll = Boolean(payload?.resetScroll);
      if (shouldResetScroll) {
        desiredScrollTop = 0;
      }
      applyThemeVars(payload?.themeVars || {});
      setTheme(payload?.theme === 'dark' ? 'dark' : 'light');
      setText(title, payload?.title || 'Student Send List');
      setText(subtitle, payload?.subtitle || (rows.length + ' students'));
      list.querySelectorAll('.empty').forEach((node) => node.remove());
      if (!rows.length) {
        const empty = document.createElement('div');
        empty.className = 'empty';
        empty.textContent = 'No students available.';
        list.replaceChildren(empty);
        rowNodes.clear();
        restoreManagedScroll();
        return;
      }
      const seen = new Set();
      for (const [index, row] of rows.entries()) {
        const regNo = String(row.regNo || '');
        if (!regNo) continue;
        let node = rowNodes.get(regNo);
        if (!node) {
          node = makeRow(row);
          rowNodes.set(regNo, node);
        }
        seen.add(regNo);
        const rowElement = patchRow(node, row);
        if (list.children[index] !== rowElement) {
          list.insertBefore(rowElement, list.children[index] || null);
        }
      }
      for (const [regNo, node] of rowNodes.entries()) {
        if (!seen.has(regNo)) {
          node.item.remove();
          rowNodes.delete(regNo);
        }
      }
      if (shouldResetScroll) {
        resetManagedScroll();
        requestAnimationFrame(resetManagedScroll);
        return;
      }
      restoreManagedScroll();
      requestAnimationFrame(restoreManagedScroll);
    }
    document.querySelector('.back').addEventListener('click', () => window.__SHINE_DESKTOP__?.closeFloatingSendWindow?.('back'));
    document.querySelector('.close').addEventListener('click', () => window.__SHINE_DESKTOP__?.closeFloatingSendWindow?.('close'));
    themeButton.addEventListener('click', () => setTheme(document.body.classList.contains('light-theme') ? 'dark' : 'light'));
    window.__SHINE_DESKTOP__?.onFloatingSendUpdate?.(render);
  </script>
</body>
</html>`;
}

function keepFloatingSendWindowOnTop() {
  if (!floatingSendWindow || floatingSendWindow.isDestroyed()) return;
  floatingSendWindow.setAlwaysOnTop(true, 'floating');
}

function restoreMainWindowFromFloating(reason = 'close') {
  floatingSendPayload = null;
  floatingSendResetOnNextShow = true;
  if (!mainWindowRef || mainWindowRef.isDestroyed()) return;
  maximizeMainWindow();
  mainWindowRef.webContents.send('shine:floatingSend:closed', { reason });
  mainWindowRef.show();
  mainWindowRef.focus();
  if (pendingUpdateInfo?.available && desktopSettings.autoInstallUpdatesWhenIdle) {
    setTimeout(() => void promptAndInstallDesktopUpdate(pendingUpdateInfo), 700);
  }
}

async function showFloatingSendWindow(payload) {
  floatingSendPayload = normalizeFloatingSendPayload(payload || {});
  if (!mainWindowRef) {
    return { success: false, error: 'Main window is not available.' };
  }

  if (!floatingSendWindow || floatingSendWindow.isDestroyed()) {
    floatingSendWindow = new BrowserWindow({
      ...getFloatingSendBounds(),
      minWidth: 330,
      minHeight: 420,
      maxWidth: 520,
      alwaysOnTop: true,
      frame: false,
      skipTaskbar: true,
      resizable: true,
      movable: true,
      autoHideMenuBar: true,
      backgroundColor: '#0b1220',
      title: 'Shine Student Send List',
      webPreferences: {
        contextIsolation: true,
        nodeIntegration: false,
        backgroundThrottling: false,
        preload: resolve(currentDir, 'preload.cjs'),
      },
    });
    keepFloatingSendWindowOnTop();
    floatingSendWindow.on('closed', () => {
      const reason = floatingSendCloseReason;
      if (floatingSendPayload?.mode === 'web') {
        void closeManagedWhatsappWebWindow();
      }
      floatingSendCloseReason = 'closed';
      floatingSendWindow = null;
      restoreMainWindowFromFloating(reason);
    });
    const html = buildFloatingSendHtml();
    const dataUrl = `data:text/html;charset=utf-8,${encodeURIComponent(html)}`;
    await floatingSendWindow.loadURL(dataUrl);
  }

  keepFloatingSendWindowOnTop();
  const resetScroll = floatingSendResetOnNextShow;
  if (resetScroll) {
    floatingSendWindow.setBounds(getFloatingSendBounds());
  }
  floatingSendWindow.show();
  floatingSendResetOnNextShow = false;
  if (mainWindowRef && !mainWindowRef.isDestroyed() && mainWindowRef.isVisible()) {
    mainWindowRef.hide();
  }
  floatingSendWindow.webContents.send('shine:floatingSend:update', {
    ...floatingSendPayload,
    resetScroll,
  });
  if (resetScroll) {
    floatingSendWindow.webContents.executeJavaScript(`
      (() => {
        const list = document.getElementById('floatingList');
        if (!list) return;
        const reset = () => list.scrollTo({ top: 0, left: 0, behavior: 'auto' });
        reset();
        requestAnimationFrame(reset);
        setTimeout(reset, 80);
      })();
    `, true).catch(() => {});
  }
  return { success: true };
}

async function closeFloatingSendWindow(reason = 'close') {
  const safeReason = String(reason || 'close');
  if (safeReason === 'inactive') {
    return { success: true };
  }
  if (floatingSendPayload?.mode === 'web') {
    await closeManagedWhatsappWebWindow();
  }
  if (floatingSendWindow && !floatingSendWindow.isDestroyed()) {
    floatingSendWindow.hide();
    restoreMainWindowFromFloating(safeReason);
  } else if (mainWindowRef && !mainWindowRef.isDestroyed()) {
    restoreMainWindowFromFloating(safeReason);
  }
  return { success: true };
}

function boundsMatch(currentBounds, nextBounds) {
  if (!currentBounds || !nextBounds) return false;
  return currentBounds.x === nextBounds.x
    && currentBounds.y === nextBounds.y
    && currentBounds.width === nextBounds.width
    && currentBounds.height === nextBounds.height;
}

function getHttpClientForTarget(targetUrl) {
  return targetUrl.protocol === 'https:' ? https : http;
}

function resolveStaticAssetPath(urlPathname) {
  const trimmed = String(urlPathname || '/').trim();
  const relativePath = decodeURIComponent(trimmed === '/' ? '/index.html' : trimmed);
  const candidate = resolve(clientDistRoot, `.${relativePath}`);
  if (!candidate.startsWith(clientDistRoot)) return null;
  return candidate;
}

function sendSimpleHtml(res, statusCode, title, body) {
  res.writeHead(statusCode, { 'Content-Type': 'text/html; charset=utf-8' });
  res.end(`<!doctype html><html><head><meta charset="utf-8" /><title>${title}</title><style>body{font-family:Segoe UI,system-ui,sans-serif;background:#0b1220;color:#e6edf8;display:grid;place-items:center;min-height:100vh;margin:0}main{max-width:720px;padding:32px;border:1px solid rgba(148,163,184,.28);border-radius:24px;background:rgba(15,23,42,.88);box-shadow:0 30px 80px rgba(2,6,23,.45)}h1{margin:0 0 12px;font-size:1.6rem}p{margin:0 0 12px;color:#bdd0f4;line-height:1.5}code{background:rgba(15,23,42,.75);padding:2px 8px;border-radius:999px}</style></head><body><main><h1>${title}</h1><p>${body}</p></main></body></html>`);
}

async function serveRendererAsset(req, res, requestUrl) {
  const assetPath = resolveStaticAssetPath(requestUrl.pathname);
  if (!assetPath) {
    sendSimpleHtml(res, 403, 'Blocked path', 'The requested renderer asset could not be resolved.');
    return;
  }

  const requestedExtension = extname(assetPath).toLowerCase();
  const isDirectAssetRequest = requestedExtension.length > 0;
  let filePath = assetPath;

  if (!existsSync(filePath)) {
    if (isDirectAssetRequest) {
      sendSimpleHtml(res, 404, 'Missing asset', 'The desktop shell could not find the requested built asset.');
      return;
    }
    filePath = resolve(clientDistRoot, 'index.html');
  }

  try {
    const fileStat = await stat(filePath);
    if (!fileStat.isFile()) {
      sendSimpleHtml(res, 404, 'Invalid asset', 'The resolved desktop asset is not a file.');
      return;
    }
  } catch {
    sendSimpleHtml(res, 404, 'Missing app build', 'Build the client first with `npm run build --prefix client` before launching desktop app mode.');
    return;
  }

  const mimeType = MIME_TYPES[extname(filePath).toLowerCase()] || 'application/octet-stream';
  res.writeHead(200, {
    'Content-Type': mimeType,
    'Cache-Control': filePath.endsWith('index.html') ? 'no-store' : 'public, max-age=31536000, immutable',
  });
  createReadStream(filePath).pipe(res);
}

function proxyApiRequest(req, res, requestUrl) {
  const targetUrl = new URL(`${requestUrl.pathname}${requestUrl.search}`, apiOrigin);
  const requestClient = getHttpClientForTarget(targetUrl);
  const proxyRequest = requestClient.request(targetUrl, {
    method: req.method,
    headers: {
      ...req.headers,
      host: targetUrl.host,
      origin: shellOrigin,
      referer: `${shellOrigin}/`,
    },
  }, (proxyResponse) => {
    res.writeHead(proxyResponse.statusCode || 502, proxyResponse.headers);
    proxyResponse.pipe(res);
  });

  proxyRequest.on('error', (error) => {
    sendSimpleHtml(res, 502, 'Backend unavailable', `The desktop shell could not reach the Shine server at <code>${apiOrigin}</code>. ${error instanceof Error ? error.message : 'Proxy request failed.'}`);
  });

  req.pipe(proxyRequest);
}

async function startDesktopShellServer() {
  if (shellServer) return shellOrigin;

  try {
    await access(resolve(clientDistRoot, 'index.html'), fsConstants.R_OK);
  } catch {
    throw new Error('Client build output is missing. Run `npm run build --prefix client` before starting desktop app mode.');
  }

  shellServer = http.createServer((req, res) => {
    const requestUrl = new URL(req.url || '/', shellOrigin);
    if (requestUrl.pathname.startsWith('/api/') || requestUrl.pathname.startsWith('/auth/')) {
      proxyApiRequest(req, res, requestUrl);
      return;
    }
    void serveRendererAsset(req, res, requestUrl);
  });

  await new Promise((resolvePromise, rejectPromise) => {
    shellServer.once('error', rejectPromise);
    shellServer.listen(shellPort, shellHost, () => {
      shellServer.off('error', rejectPromise);
      resolvePromise();
    });
  });

  return shellOrigin;
}

async function waitForRenderer(url, attempts = 80, intervalMs = 500) {
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    try {
      const response = await fetch(url, { method: 'GET' });
      if (response.ok) return;
    } catch {
      // Keep waiting for the renderer target to come up.
    }
    await new Promise((resolvePromise) => setTimeout(resolvePromise, intervalMs));
  }
  throw new Error(`Timed out waiting for renderer target ${url}`);
}

function attachExternalNavigationGuards(targetWebContents, internalOrigin) {
  if (!targetWebContents) return;

  targetWebContents.setWindowOpenHandler(({ url }) => {
    if (url.startsWith(internalOrigin)) return { action: 'allow' };
    void shell.openExternal(url);
    return { action: 'deny' };
  });

  targetWebContents.on('will-navigate', (event, url) => {
    if (url.startsWith(internalOrigin)) return;
    event.preventDefault();
    void shell.openExternal(url);
  });
}

function findExecutable(candidates) {
  for (const candidate of candidates) {
    if (!candidate) continue;
    if (existsSync(candidate)) return candidate;
    const result = spawnSync('where.exe', [candidate], {
      windowsHide: true,
      stdio: ['ignore', 'pipe', 'ignore'],
      encoding: 'utf8',
    });
    if (result.status === 0) {
      const firstMatch = String(result.stdout || '')
        .split(/\r?\n/)
        .map((line) => line.trim())
        .find(Boolean);
      if (firstMatch) return firstMatch;
    }
  }
  return '';
}

function hasAppxPackage(packageQuery) {
  const safeQuery = String(packageQuery || '').trim();
  if (!safeQuery) return false;
  const result = spawnSync('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    `if (Get-AppxPackage ${safeQuery} -ErrorAction SilentlyContinue) { '1' }`,
  ], {
    windowsHide: true,
    stdio: ['ignore', 'pipe', 'ignore'],
    encoding: 'utf8',
  });
  return result.status === 0 && String(result.stdout || '').trim() === '1';
}

function resolveWhatsappDesktopExecutable() {
  const localAppData = String(process.env.LOCALAPPDATA || '').trim();
  const directMatch = findExecutable([
    resolve(localAppData, 'WhatsApp\\WhatsApp.exe'),
    resolve(localAppData, 'Microsoft\\WindowsApps\\WhatsApp.exe'),
    'WhatsApp.exe',
    'WhatsApp',
  ]);
  if (directMatch) return directMatch;

  const result = spawnSync('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    `
$pkg = Get-AppxPackage *WhatsApp* -ErrorAction SilentlyContinue | Select-Object -First 1
if ($pkg) {
  $candidate = Join-Path $pkg.InstallLocation 'WhatsApp.Root.exe'
  if (Test-Path $candidate) {
    Write-Output $candidate
  }
}
`,
  ], {
    windowsHide: true,
    stdio: ['ignore', 'pipe', 'ignore'],
    encoding: 'utf8',
  });
  const packageExecutable = String(result.stdout || '')
    .split(/\r?\n/)
    .map((line) => line.trim())
    .find(Boolean);
  return packageExecutable && existsSync(packageExecutable) ? packageExecutable : '';
}

function getAvailableSendTargets() {
  const chromePath = findExecutable([
    'chrome.exe',
    'chrome',
    resolve(process.env['ProgramFiles'] || 'C:\\Program Files', 'Google\\Chrome\\Application\\chrome.exe'),
    resolve(process.env['ProgramFiles(x86)'] || 'C:\\Program Files (x86)', 'Google\\Chrome\\Application\\chrome.exe'),
  ]);
  const edgePath = findExecutable([
    'msedge.exe',
    'msedge',
    resolve(process.env['ProgramFiles(x86)'] || 'C:\\Program Files (x86)', 'Microsoft\\Edge\\Application\\msedge.exe'),
    resolve(process.env['ProgramFiles'] || 'C:\\Program Files', 'Microsoft\\Edge\\Application\\msedge.exe'),
  ]);
  const whatsappPath = resolveWhatsappDesktopExecutable();
  const whatsappDesktopInstalled = Boolean(whatsappPath) || hasAppxPackage('*WhatsApp*');

  return {
    default_browser: true,
    chrome: Boolean(chromePath),
    edge: Boolean(edgePath),
    whatsapp_desktop: whatsappDesktopInstalled,
    paths: {
      chrome: chromePath,
      edge: edgePath,
      whatsapp_desktop: whatsappPath,
    },
  };
}

function launchDetached(executable, args) {
  const child = spawn(executable, args, {
    detached: true,
    stdio: 'ignore',
    windowsHide: true,
  });
  child.unref();
}

function launchGuiProcess(executable, args) {
  const safeExecutable = String(executable || '').trim();
  if (!safeExecutable) return;
  const child = spawn(safeExecutable, (args || []).map((value) => String(value)), {
    detached: true,
    stdio: 'ignore',
    windowsHide: false,
    shell: false,
  });
  child.unref();
}

function launchWindowsUri(uri) {
  const safeUri = String(uri || '').trim();
  if (!safeUri) return false;
  const result = spawnSync('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    `Start-Process ${JSON.stringify(safeUri)}`,
  ], {
    windowsHide: true,
    stdio: ['ignore', 'ignore', 'ignore'],
    encoding: 'utf8',
  });
  return result.status === 0;
}

function launchWindowsExecutable(executable, args = []) {
  const safeExecutable = String(executable || '').trim();
  if (!safeExecutable) return false;
  const safeArgs = Array.isArray(args) ? args.map((value) => String(value || '').trim()).filter(Boolean) : [];
  const result = spawnSync('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    `
$argList = ${JSON.stringify(safeArgs)} | ConvertFrom-Json
Start-Process -FilePath ${JSON.stringify(safeExecutable)} -ArgumentList $argList
`,
  ], {
    windowsHide: true,
    stdio: ['ignore', 'ignore', 'ignore'],
    encoding: 'utf8',
  });
  return result.status === 0;
}

function launchAppUserModelId(appId) {
  const safeAppId = String(appId || '').trim();
  if (!safeAppId) return false;
  const result = spawnSync('explorer.exe', [`shell:AppsFolder\\${safeAppId}`], {
    windowsHide: true,
    stdio: ['ignore', 'ignore', 'ignore'],
    encoding: 'utf8',
  });
  return result.status === 0;
}

function getWorkspaceBrowserProfileDir(target) {
  const profileRoot = resolve(desktopRoot, '.workspace', 'send-browser-profiles');
  mkdirSync(profileRoot, { recursive: true });
  return resolve(profileRoot, target === 'edge' ? 'edge' : 'chrome');
}

async function delay(ms) {
  await new Promise((resolvePromise) => setTimeout(resolvePromise, ms));
}

async function waitForExternalWindow(processNames, profileDir = '', attempts = 32, delayMs = 250) {
  for (let attempt = 0; attempt < attempts; attempt += 1) {
    if (processWindowExists(processNames, profileDir)) {
      return true;
    }
    await delay(delayMs);
  }
  return false;
}

function moveMainWindowToBounds(bounds) {
  if (!mainWindowRef || !bounds) return;
  if (mainWindowRef.isMinimized()) mainWindowRef.restore();
  if (mainWindowRef.isMaximized()) mainWindowRef.unmaximize();
  if (mainWindowRef.isFullScreen()) mainWindowRef.setFullScreen(false);
  mainWindowRef.setBounds(bounds, true);
  mainWindowRef.setPosition(bounds.x, bounds.y, true);
  mainWindowRef.setSize(bounds.width, bounds.height, true);
  mainWindowRef.show();
}

function maximizeMainWindow() {
  if (!mainWindowRef) return;
  if (mainWindowRef.isMinimized()) mainWindowRef.restore();
  if (mainWindowRef.isFullScreen()) mainWindowRef.setFullScreen(false);
  if (!mainWindowRef.isMaximized()) {
    mainWindowRef.maximize();
  }
  mainWindowRef.show();
}

function getDesktopWorkspaceWindowBounds() {
  if (!mainWindowRef) return null;
  const display = screen.getDisplayMatching(mainWindowRef.getBounds());
  const workArea = display?.workArea || screen.getPrimaryDisplay().workArea;
  return {
    x: workArea.x,
    y: workArea.y,
    width: Math.max(DEFAULT_MAIN_MIN_WIDTH, workArea.width),
    height: Math.max(DEFAULT_MAIN_MIN_HEIGHT, workArea.height),
  };
}

function getEmbeddedWhatsappBounds() {
  if (!mainWindowRef) return null;
  const contentBounds = mainWindowRef.getContentBounds();
  const gap = 8;
  const sideWidth = DESKTOP_WORKSPACE_MIN_WIDTH;
  const viewWidth = Math.max(720, contentBounds.width - sideWidth - gap);
  return {
    x: 0,
    y: 0,
    width: Math.max(0, viewWidth),
    height: Math.max(0, contentBounds.height),
  };
}

function syncEmbeddedWhatsappBounds() {
  if (!desktopWorkspaceActive || !desktopWhatsappView || !mainWindowRef) return;
  const bounds = getEmbeddedWhatsappBounds();
  if (!bounds) return;
  desktopWhatsappView.setBounds(bounds);
  if (typeof desktopWhatsappView.setAutoResize === 'function') {
    desktopWhatsappView.setAutoResize({ width: true, height: true });
  }
}

function collapseEmbeddedWhatsappView() {
  if (!desktopWhatsappView) return;
  desktopWhatsappView.setBounds({ x: 0, y: 0, width: 0, height: 0 });
  if (typeof desktopWhatsappView.setAutoResize === 'function') {
    desktopWhatsappView.setAutoResize({ width: false, height: false });
  }
}

function detachDesktopWhatsappView() {
  if (!mainWindowRef || !desktopWhatsappView) return;
  try {
    if (typeof mainWindowRef.removeBrowserView === 'function') {
      mainWindowRef.removeBrowserView(desktopWhatsappView);
    } else if (mainWindowRef.contentView && typeof mainWindowRef.contentView.removeChildView === 'function') {
      mainWindowRef.contentView.removeChildView(desktopWhatsappView);
    }
    desktopWhatsappViewAttached = false;
  } catch {
    // Ignore duplicate detach attempts.
  }
}

function configureDesktopWhatsappView(view) {
  view.webContents.setUserAgent(EMBEDDED_WHATSAPP_USER_AGENT);
  view.webContents.setAudioMuted(true);
  view.webContents.on('did-start-loading', () => {
    desktopWhatsappViewLoading = true;
  });
  view.webContents.on('did-stop-loading', () => {
    desktopWhatsappViewLoading = false;
  });
  view.webContents.on('did-fail-load', () => {
    desktopWhatsappViewLoading = false;
  });
  view.webContents.on('destroyed', () => {
    desktopWhatsappViewLoading = false;
  });
  view.webContents.session.setPermissionRequestHandler((_webContents, permission, callback) => {
    if (permission === 'notifications' || permission === 'media' || permission === 'midi' || permission === 'pointerLock') {
      callback(false);
      return;
    }
    callback(false);
  });
  view.webContents.setWindowOpenHandler(({ url }) => {
    if (String(url || '').startsWith('https://web.whatsapp.com/')) {
      return { action: 'allow' };
    }
    void shell.openExternal(url);
    return { action: 'deny' };
  });
}

function ensureDesktopWhatsappView() {
  if (desktopWhatsappView && !desktopWhatsappView.webContents.isDestroyed()) {
    return desktopWhatsappView;
  }
  if (!EmbeddedBrowserView) {
    throw new Error('This Electron runtime does not expose BrowserView or WebContentsView.');
  }
  const view = new EmbeddedBrowserView({
    webPreferences: {
      contextIsolation: true,
      nodeIntegration: false,
      sandbox: true,
      partition: 'persist:shine-desktop-whatsapp',
      spellcheck: false,
      autoplayPolicy: 'user-gesture-required',
    },
  });
  configureDesktopWhatsappView(view);
  desktopWhatsappView = view;
  return desktopWhatsappView;
}

function attachDesktopWhatsappView() {
  if (!mainWindowRef) return null;
  const view = ensureDesktopWhatsappView();
  const attachedViews = typeof mainWindowRef.getBrowserViews === 'function'
    ? mainWindowRef.getBrowserViews()
    : [];
  if (typeof mainWindowRef.addBrowserView === 'function' && !attachedViews.includes(view)) {
    mainWindowRef.addBrowserView(view);
    desktopWhatsappViewAttached = true;
  } else if (!desktopWhatsappViewAttached && mainWindowRef.contentView && typeof mainWindowRef.contentView.addChildView === 'function') {
    mainWindowRef.contentView.addChildView(view);
    desktopWhatsappViewAttached = true;
  }
  void clearDesktopWhatsappExitOverlay(view);
  syncEmbeddedWhatsappBounds();
  return view;
}

async function clearDesktopWhatsappExitOverlay(view) {
  if (!view?.webContents || view.webContents.isDestroyed()) return;
  try {
    await view.webContents.executeJavaScript(
      `(() => {
        const overlay = document.getElementById('__shine_exit_fade__');
        if (overlay) overlay.remove();
        return true;
      })();`,
      true,
    );
  } catch {
    // Ignore cleanup issues while the view is booting or navigating.
  }
}

async function fadeOutDesktopWhatsappView(durationMs = 180) {
  const view = desktopWhatsappView;
  if (!view?.webContents || view.webContents.isDestroyed()) return;
  try {
    await view.webContents.executeJavaScript(
      `(() => {
        const existing = document.getElementById('__shine_exit_fade__');
        if (existing) existing.remove();
        const bodyBackground = getComputedStyle(document.body).backgroundColor;
        const htmlBackground = getComputedStyle(document.documentElement).backgroundColor;
        const overlay = document.createElement('div');
        overlay.id = '__shine_exit_fade__';
        Object.assign(overlay.style, {
          position: 'fixed',
          inset: '0',
          zIndex: '2147483647',
          pointerEvents: 'none',
          opacity: '0',
          background: bodyBackground && bodyBackground !== 'rgba(0, 0, 0, 0)' ? bodyBackground : (htmlBackground || '#0a0c14'),
          transition: 'opacity ${durationMs}ms ease',
        });
        document.documentElement.appendChild(overlay);
        requestAnimationFrame(() => {
          overlay.style.opacity = '1';
        });
        return true;
      })();`,
      true,
    );
    await delay(durationMs);
  } catch {
    // Ignore fade failures and fall back to an instant collapse.
  }
}

async function navigateEmbeddedWhatsappView(url) {
  const view = attachDesktopWhatsappView();
  if (!view) return false;
  const targetUrl = String(url || '').trim();
  if (!targetUrl) return false;
  desktopWhatsappViewLoading = true;
  const debuggerClient = view.webContents.debugger;
  try {
    if (!debuggerClient.isAttached()) {
      debuggerClient.attach('1.3');
    }
  } catch (error) {
    const message = error instanceof Error ? error.message : '';
    if (!/already attached/i.test(message)) {
      throw error;
    }
  }

  try {
    await debuggerClient.sendCommand('Page.enable');
  } catch {
    // Ignore enable failures and still attempt navigation below.
  }

  await debuggerClient.sendCommand('Page.navigate', { url: targetUrl });
  return true;
}

async function handoffEmbeddedWhatsappView(url) {
  const view = attachDesktopWhatsappView();
  if (!view?.webContents) return false;
  const targetUrl = String(url || '').trim();
  if (!targetUrl) return false;
  desktopWhatsappViewLoading = true;
  try {
    const result = await view.webContents.executeJavaScript(
      `(() => {
        const nextUrl = ${JSON.stringify(targetUrl)};
        if (!nextUrl) return 'empty';
        if (window.location.href === nextUrl) return 'same';
        const existing = document.querySelector('a[data-shine-whatsapp-handoff="true"]');
        if (existing) existing.remove();
        const anchor = document.createElement('a');
        anchor.href = nextUrl;
        anchor.target = '_self';
        anchor.rel = 'noreferrer noopener';
        anchor.dataset.shineWhatsappHandoff = 'true';
        anchor.style.position = 'fixed';
        anchor.style.left = '-9999px';
        anchor.style.top = '-9999px';
        document.body.appendChild(anchor);
        anchor.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true, view: window }));
        anchor.click();
        setTimeout(() => anchor.remove(), 1500);
        return 'clicked';
      })();`,
      true,
    );
    return result === 'clicked' || result === 'same';
  } catch {
    return false;
  }
}

async function waitForWhatsappViewLoad(view, timeoutMs = 4500) {
  if (!view?.webContents) return false;
  if (!view.webContents.isLoadingMainFrame()) return true;
  await new Promise((resolve) => {
    let settled = false;
    const finish = () => {
      if (settled) return;
      settled = true;
      cleanup();
      resolve(true);
    };
    const cleanup = () => {
      try {
        view.webContents.removeListener('did-stop-loading', finish);
        view.webContents.removeListener('did-fail-load', finish);
        view.webContents.removeListener('destroyed', finish);
      } catch {
        // Ignore cleanup issues.
      }
    };
    view.webContents.once('did-stop-loading', finish);
    view.webContents.once('did-fail-load', finish);
    view.webContents.once('destroyed', finish);
    setTimeout(finish, timeoutMs);
  });
  return true;
}

async function loadDesktopWhatsappTarget(url = EMBEDDED_WHATSAPP_URL) {
  const view = attachDesktopWhatsappView();
  if (!view) return false;
  const targetUrl = String(url || '').trim() || EMBEDDED_WHATSAPP_URL;
  const currentUrl = String(view.webContents.getURL() || '').trim();
  if (currentUrl === targetUrl) {
    syncEmbeddedWhatsappBounds();
    return true;
  }
  const isWhatsappNavigation = currentUrl.startsWith('https://web.whatsapp.com/')
    && targetUrl.startsWith('https://web.whatsapp.com/');
  if (isWhatsappNavigation) {
    try {
      const handedOff = await handoffEmbeddedWhatsappView(targetUrl);
      if (handedOff) {
        await waitForWhatsappViewLoad(view, 2500);
        syncEmbeddedWhatsappBounds();
        return true;
      }
      collapseEmbeddedWhatsappView();
      await navigateEmbeddedWhatsappView(targetUrl);
      await waitForWhatsappViewLoad(view);
      syncEmbeddedWhatsappBounds();
      return true;
    } catch {
      // Fall back to a normal same-view navigation if debugger routing is unavailable.
    }
  }
  collapseEmbeddedWhatsappView();
  desktopWhatsappViewLoading = true;
  await view.webContents.loadURL(targetUrl, { userAgent: EMBEDDED_WHATSAPP_USER_AGENT });
  desktopWhatsappViewLoading = false;
  syncEmbeddedWhatsappBounds();
  return true;
}

function processWindowExists(processNames, profileDir = '') {
  const safeNames = processNames.filter(Boolean);
  if (!safeNames.length) return false;
  const encodedNames = JSON.stringify(safeNames);
  const encodedProfileDir = JSON.stringify(String(profileDir || ''));
  const result = spawnSync('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    `
$names = ${encodedNames} | ConvertFrom-Json;
$profileDir = ${encodedProfileDir};
$matchIds = @();
if ($profileDir) {
  $matchIds = Get-CimInstance Win32_Process | Where-Object {
    ($names -contains $_.Name.Replace('.exe','')) -and $_.CommandLine -and $_.CommandLine.Contains($profileDir)
  } | Select-Object -ExpandProperty ProcessId;
}
$priority = @{};
for ($idx = 0; $idx -lt $names.Count; $idx++) {
  $priority[$names[$idx]] = $idx;
}
$hit = if ($profileDir) {
  if ($matchIds.Count -gt 0) {
    Get-Process -Id $matchIds -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowHandle -ne 0 } | Select-Object -First 1
  } else {
    $null
  }
} elseif ($matchIds.Count -gt 0) {
  Get-Process -Id $matchIds -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowHandle -ne 0 } | Select-Object -First 1
} else {
  $named = Get-Process | Where-Object { $names -contains $_.ProcessName -and $_.MainWindowHandle -ne 0 } | Sort-Object @{Expression = { $priority[$_.ProcessName] }}, @{Expression = { $_.StartTime }; Descending = $true } | Select-Object -First 1;
  if ($named) {
    $named
  } elseif ($names -contains 'WhatsApp.Root' -or $names -contains 'ApplicationFrameHost' -or $names -contains 'msedgewebview2') {
    Get-Process | Where-Object {
      $_.MainWindowHandle -ne 0 -and
      ($_.ProcessName -eq 'WhatsApp.Root' -or $_.ProcessName -eq 'ApplicationFrameHost' -or $_.ProcessName -eq 'msedgewebview2') -and
      $_.MainWindowTitle -match 'WhatsApp'
    } | Sort-Object StartTime -Descending | Select-Object -First 1
  } else {
    $null
  }
};
if ($hit) { '1' }
`,
  ], {
    windowsHide: true,
    stdio: ['ignore', 'pipe', 'ignore'],
    encoding: 'utf8',
  });
  return result.status === 0 && String(result.stdout || '').trim() === '1';
}

function repositionExternalWindow(processNames, bounds, profileDir = '') {
  const safeNames = processNames.filter(Boolean);
  if (!safeNames.length || !bounds) return;
  const encodedNames = JSON.stringify(safeNames);
  const encodedProfileDir = JSON.stringify(String(profileDir || ''));
  const script = `
Add-Type @"
using System;
using System.Runtime.InteropServices;
public static class WinApi {
  [DllImport("user32.dll")] public static extern bool SetWindowPos(IntPtr hWnd, IntPtr hWndInsertAfter, int X, int Y, int cx, int cy, uint uFlags);
  [DllImport("user32.dll")] public static extern bool ShowWindowAsync(IntPtr hWnd, int nCmdShow);
}
"@;
$names = ${encodedNames} | ConvertFrom-Json;
$profileDir = ${encodedProfileDir};
$priority = @{};
for ($idx = 0; $idx -lt $names.Count; $idx++) {
  $priority[$names[$idx]] = $idx;
}
for ($i = 0; $i -lt 40; $i++) {
  $matchIds = @();
  if ($profileDir) {
    $matchIds = Get-CimInstance Win32_Process | Where-Object {
      ($names -contains $_.Name.Replace('.exe','')) -and $_.CommandLine -and $_.CommandLine.Contains($profileDir)
    } | Select-Object -ExpandProperty ProcessId;
  }
  $proc = if ($profileDir) {
    if ($matchIds.Count -gt 0) {
      Get-Process -Id $matchIds -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowHandle -ne 0 } | Sort-Object StartTime -Descending | Select-Object -First 1
    } else {
      $null
    }
  } elseif ($matchIds.Count -gt 0) {
    Get-Process -Id $matchIds -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowHandle -ne 0 } | Sort-Object StartTime -Descending | Select-Object -First 1
  } else {
    $named = Get-Process | Where-Object { $names -contains $_.ProcessName -and $_.MainWindowHandle -ne 0 } | Sort-Object @{Expression = { $priority[$_.ProcessName] }}, @{Expression = { $_.StartTime }; Descending = $true } | Select-Object -First 1;
    if ($named) {
      $named
    } elseif ($names -contains 'WhatsApp.Root' -or $names -contains 'ApplicationFrameHost' -or $names -contains 'msedgewebview2') {
      Get-Process | Where-Object {
        $_.MainWindowHandle -ne 0 -and
        ($_.ProcessName -eq 'WhatsApp.Root' -or $_.ProcessName -eq 'ApplicationFrameHost' -or $_.ProcessName -eq 'msedgewebview2') -and
        $_.MainWindowTitle -match 'WhatsApp'
      } | Sort-Object StartTime -Descending | Select-Object -First 1
    } else {
      $null
    }
  };
  if ($proc) {
    [WinApi]::ShowWindowAsync($proc.MainWindowHandle, 9) | Out-Null;
    [WinApi]::SetWindowPos($proc.MainWindowHandle, [IntPtr]::Zero, ${bounds.x}, ${bounds.y}, ${bounds.width}, ${bounds.height}, 0x0040) | Out-Null;
    break;
  }
  Start-Sleep -Milliseconds 350;
}
`;

  spawn('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    script,
  ], {
    detached: true,
    stdio: 'ignore',
    windowsHide: true,
  }).unref();
}

function maximizeExternalWindow(processNames, profileDir = '') {
  const safeNames = processNames.filter(Boolean);
  if (!safeNames.length) return;
  const encodedNames = JSON.stringify(safeNames);
  const encodedProfileDir = JSON.stringify(String(profileDir || ''));
  const script = `
Add-Type @"
using System;
using System.Runtime.InteropServices;
public static class WinApi {
  [DllImport("user32.dll")] public static extern bool ShowWindowAsync(IntPtr hWnd, int nCmdShow);
}
"@;
$names = ${encodedNames} | ConvertFrom-Json;
$profileDir = ${encodedProfileDir};
$priority = @{};
for ($idx = 0; $idx -lt $names.Count; $idx++) {
  $priority[$names[$idx]] = $idx;
}
for ($i = 0; $i -lt 40; $i++) {
  $matchIds = @();
  if ($profileDir) {
    $matchIds = Get-CimInstance Win32_Process | Where-Object {
      ($names -contains $_.Name.Replace('.exe','')) -and $_.CommandLine -and $_.CommandLine.Contains($profileDir)
    } | Select-Object -ExpandProperty ProcessId;
  }
  $proc = if ($profileDir) {
    if ($matchIds.Count -gt 0) {
      Get-Process -Id $matchIds -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowHandle -ne 0 } | Sort-Object StartTime -Descending | Select-Object -First 1
    } else {
      $null
    }
  } elseif ($matchIds.Count -gt 0) {
    Get-Process -Id $matchIds -ErrorAction SilentlyContinue | Where-Object { $_.MainWindowHandle -ne 0 } | Sort-Object StartTime -Descending | Select-Object -First 1
  } else {
    $named = Get-Process | Where-Object { $names -contains $_.ProcessName -and $_.MainWindowHandle -ne 0 } | Sort-Object @{Expression = { $priority[$_.ProcessName] }}, @{Expression = { $_.StartTime }; Descending = $true } | Select-Object -First 1;
    if ($named) {
      $named
    } elseif ($names -contains 'WhatsApp.Root' -or $names -contains 'ApplicationFrameHost' -or $names -contains 'msedgewebview2') {
      Get-Process | Where-Object {
        $_.MainWindowHandle -ne 0 -and
        ($_.ProcessName -eq 'WhatsApp.Root' -or $_.ProcessName -eq 'ApplicationFrameHost' -or $_.ProcessName -eq 'msedgewebview2') -and
        $_.MainWindowTitle -match 'WhatsApp'
      } | Sort-Object StartTime -Descending | Select-Object -First 1
    } else {
      $null
    }
  };
  if ($proc) {
    [WinApi]::ShowWindowAsync($proc.MainWindowHandle, 3) | Out-Null;
    break;
  }
  Start-Sleep -Milliseconds 350;
}
`;

  spawn('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    script,
  ], {
    detached: true,
    stdio: 'ignore',
    windowsHide: true,
  }).unref();
}

function closeWorkspaceBrowserProcesses(processNames, profileDir = '') {
  const safeNames = processNames.filter(Boolean);
  if (!safeNames.length) return;
  const encodedNames = JSON.stringify(safeNames);
  const encodedProfileDir = JSON.stringify(String(profileDir || ''));
  spawnSync('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    `
$names = ${encodedNames} | ConvertFrom-Json;
$profileDir = ${encodedProfileDir};
$matchIds = @();
if ($profileDir) {
  $matchIds = Get-CimInstance Win32_Process | Where-Object {
    ($names -contains $_.Name.Replace('.exe','')) -and $_.CommandLine -and $_.CommandLine.Contains($profileDir)
  } | Select-Object -ExpandProperty ProcessId;
}
if ($matchIds.Count -gt 0) {
  Get-Process -Id $matchIds -ErrorAction SilentlyContinue | Stop-Process -Force -ErrorAction SilentlyContinue;
}
`,
  ], {
    windowsHide: true,
    stdio: ['ignore', 'ignore', 'ignore'],
    encoding: 'utf8',
  });
}

async function closeBrowserByDebugPort(debugPort) {
  const port = Number(debugPort || 0);
  if (!port || typeof WebSocket !== 'function') return false;
  try {
    const response = await fetch(`http://127.0.0.1:${port}/json/list`);
    if (!response.ok) return false;
    const targets = await response.json();
    const target = Array.isArray(targets)
      ? targets.find((candidate) => candidate?.webSocketDebuggerUrl && String(candidate.url || '').includes('web.whatsapp.com'))
        || targets.find((candidate) => candidate?.webSocketDebuggerUrl)
      : null;
    if (!target?.webSocketDebuggerUrl) return false;
    await new Promise((resolvePromise) => {
      const socket = new WebSocket(target.webSocketDebuggerUrl);
      const cleanup = () => {
        try {
          socket.close();
        } catch {
          // Ignore close failures.
        }
      };
      socket.addEventListener('open', () => {
        socket.send(JSON.stringify({
          id: 1,
          method: 'Browser.close',
        }));
      });
      socket.addEventListener('message', (event) => {
        try {
          const payload = JSON.parse(String(event.data || '{}'));
          if (payload?.id === 1) {
            cleanup();
            resolvePromise(true);
          }
        } catch {
          // Ignore parse noise from other events.
        }
      });
      socket.addEventListener('error', () => {
        cleanup();
        resolvePromise(false);
      });
      socket.addEventListener('close', () => {
        resolvePromise(true);
      });
      setTimeout(() => {
        cleanup();
        resolvePromise(false);
      }, 2000);
    });
    return true;
  } catch {
    return false;
  }
}

async function closeManagedWhatsappWebWindow() {
  const session = desktopWorkspaceBrowserSession;
  await closeBrowserByDebugPort(session?.debugPort);
  const closeTargets = [
    { processNames: session?.processNames || ['chrome'], profileDir: session?.profileDir || getWorkspaceBrowserProfileDir('chrome') },
    { processNames: ['msedge'], profileDir: getWorkspaceBrowserProfileDir('edge') },
  ];
  for (const target of closeTargets) {
    if (target.profileDir) closeWorkspaceBrowserProcesses(target.processNames, target.profileDir);
  }
  desktopWorkspaceBrowserSession = {
    target: null,
    debugPort: 0,
    profileDir: '',
    processNames: [],
  };
}

function getDesktopWorkspaceBounds() {
  if (!mainWindowRef) return null;
  const display = screen.getDisplayMatching(mainWindowRef.getBounds());
  const workArea = display?.workArea || screen.getPrimaryDisplay().workArea;
  const gap = 8;
  const sideWidth = DESKTOP_WORKSPACE_MIN_WIDTH;
  const height = Math.max(DESKTOP_WORKSPACE_MIN_HEIGHT, workArea.height);
  const y = workArea.y;
  const browserX = workArea.x;
  const shineX = workArea.x + workArea.width - sideWidth;
  const browserWidth = Math.max(520, shineX - browserX - gap);

  return {
    workArea,
    left: {
      x: browserX,
      y,
      width: browserWidth,
      height,
    },
    right: {
      x: shineX,
      y,
      width: sideWidth,
      height,
    },
  };
}

function normalizeDesktopTarget(rawTarget) {
  const candidate = String(rawTarget || '').trim().toLowerCase();
  if (candidate === 'chrome' || candidate === 'edge' || candidate === 'whatsapp_desktop') return candidate;
  return 'default_browser';
}

function buildTargetChain(preference) {
  switch (preference) {
    case 'whatsapp_desktop':
      return ['whatsapp_desktop', 'default_browser', 'chrome', 'edge'];
    case 'chrome':
      return ['chrome', 'edge', 'default_browser', 'whatsapp_desktop'];
    case 'edge':
      return ['edge', 'chrome', 'default_browser', 'whatsapp_desktop'];
    default:
      return ['chrome', 'edge', 'default_browser', 'whatsapp_desktop'];
  }
}

function isWhatsappWebUrl(url) {
  return String(url || '').startsWith('https://web.whatsapp.com/');
}

async function navigateWorkspaceBrowserSession(url) {
  const debugPort = Number(desktopWorkspaceBrowserSession.debugPort || 0);
  if (!debugPort || typeof WebSocket !== 'function') return false;
  const targetUrl = String(url || '').trim();
  if (!targetUrl) return false;
  try {
    const response = await fetch(`http://127.0.0.1:${debugPort}/json/list`);
    if (!response.ok) return false;
    const targets = await response.json();
    const target = Array.isArray(targets)
      ? targets.find((candidate) => candidate?.webSocketDebuggerUrl && String(candidate.url || '').includes('web.whatsapp.com'))
        || targets.find((candidate) => candidate?.webSocketDebuggerUrl)
      : null;
    if (!target?.webSocketDebuggerUrl) return false;

    const sameWhatsappSession = isWhatsappWebUrl(target.url) && isWhatsappWebUrl(targetUrl);
    const handedOff = sameWhatsappSession ? await new Promise((resolvePromise) => {
      const socket = new WebSocket(target.webSocketDebuggerUrl);
      const cleanup = () => {
        try {
          socket.close();
        } catch {
          // Ignore close failures.
        }
      };
      socket.addEventListener('open', () => {
        socket.send(JSON.stringify({
          id: 1,
          method: 'Runtime.evaluate',
          params: {
            awaitPromise: false,
            returnByValue: true,
            expression: `(() => {
              const nextUrl = ${JSON.stringify(targetUrl)};
              if (!nextUrl) return 'empty';
              if (window.location.href === nextUrl) return 'same';
              const storageKey = 'shine_whatsapp_web_handoff_started';
              const hasStarted = sessionStorage.getItem(storageKey) === '1';
              const currentUrl = String(window.location.href || '');
              if (!hasStarted && !/\\/send\\//i.test(currentUrl)) {
                sessionStorage.setItem(storageKey, '1');
                window.location.assign(nextUrl);
                return 'assigned';
              }
              sessionStorage.setItem(storageKey, '1');
              const existing = document.querySelector('a[data-shine-whatsapp-handoff="true"]');
              if (existing) existing.remove();
              const anchor = document.createElement('a');
              anchor.href = nextUrl;
              anchor.target = '_self';
              anchor.rel = 'noreferrer noopener';
              anchor.dataset.shineWhatsappHandoff = 'true';
              anchor.style.position = 'fixed';
              anchor.style.left = '-9999px';
              anchor.style.top = '-9999px';
              document.body.appendChild(anchor);
              anchor.dispatchEvent(new MouseEvent('click', { bubbles: true, cancelable: true, view: window }));
              anchor.click();
              setTimeout(() => anchor.remove(), 1500);
              return 'clicked';
            })();`,
          },
        }));
      });
      socket.addEventListener('message', (event) => {
        try {
          const payload = JSON.parse(String(event.data || '{}'));
          if (payload?.id === 1) {
            const value = payload?.result?.result?.value;
            cleanup();
            resolvePromise(value === 'clicked' || value === 'same' || value === 'assigned');
          }
        } catch {
          // Ignore parse noise from other events.
        }
      });
      socket.addEventListener('error', () => {
        cleanup();
        resolvePromise(false);
      });
      setTimeout(() => {
        cleanup();
        resolvePromise(false);
      }, 2500);
    }) : false;
    if (handedOff) return true;

    await new Promise((resolvePromise, rejectPromise) => {
      const socket = new WebSocket(target.webSocketDebuggerUrl);
      const cleanup = () => {
        try {
          socket.close();
        } catch {
          // Ignore close failures.
        }
      };
      socket.addEventListener('open', () => {
        socket.send(JSON.stringify({
          id: 1,
          method: 'Page.navigate',
          params: { url: targetUrl },
        }));
      });
      socket.addEventListener('message', (event) => {
        try {
          const payload = JSON.parse(String(event.data || '{}'));
          if (payload?.id === 1) {
            cleanup();
            resolvePromise(true);
          }
        } catch {
          // Ignore parse noise from other events.
        }
      });
      socket.addEventListener('error', (error) => {
        cleanup();
        rejectPromise(error);
      });
      socket.addEventListener('close', () => {
        resolvePromise(true);
      });
      setTimeout(() => {
        cleanup();
        resolvePromise(false);
      }, 2500);
    });
    return true;
  } catch {
    return false;
  }
}

async function setWorkspaceBrowserBounds(bounds) {
  const debugPort = Number(desktopWorkspaceBrowserSession.debugPort || 0);
  if (!debugPort || typeof WebSocket !== 'function' || !bounds) return false;
  try {
    const response = await fetch(`http://127.0.0.1:${debugPort}/json/list`);
    if (!response.ok) return false;
    const targets = await response.json();
    const target = Array.isArray(targets)
      ? targets.find((candidate) => candidate?.webSocketDebuggerUrl && String(candidate.url || '').includes('web.whatsapp.com'))
        || targets.find((candidate) => candidate?.webSocketDebuggerUrl)
      : null;
    if (!target?.webSocketDebuggerUrl || !target?.id) return false;

    await new Promise((resolvePromise, rejectPromise) => {
      const socket = new WebSocket(target.webSocketDebuggerUrl);
      const cleanup = () => {
        try {
          socket.close();
        } catch {
          // Ignore close failures.
        }
      };
      let stage = 'getWindow';
      socket.addEventListener('open', () => {
        socket.send(JSON.stringify({
          id: 1,
          method: 'Browser.getWindowForTarget',
          params: { targetId: target.id },
        }));
      });
      socket.addEventListener('message', (event) => {
        try {
          const payload = JSON.parse(String(event.data || '{}'));
          if (payload?.id === 1) {
            const windowId = Number(payload?.result?.windowId || 0);
            if (!windowId) {
              cleanup();
              resolvePromise(false);
              return;
            }
            stage = 'setBounds';
            socket.send(JSON.stringify({
              id: 2,
              method: 'Browser.setWindowBounds',
              params: {
                windowId,
                bounds: {
                  left: bounds.x,
                  top: bounds.y,
                  width: bounds.width,
                  height: bounds.height,
                  windowState: 'normal',
                },
              },
            }));
            return;
          }
          if (payload?.id === 2) {
            cleanup();
            resolvePromise(true);
          }
          if (payload?.error) {
            cleanup();
            rejectPromise(new Error(stage === 'setBounds' ? 'Unable to apply browser workspace bounds.' : 'Unable to resolve browser workspace window.'));
          }
        } catch {
          // Ignore parse noise from other events.
        }
      });
      socket.addEventListener('error', (error) => {
        cleanup();
        rejectPromise(error);
      });
      setTimeout(() => {
        cleanup();
        resolvePromise(false);
      }, 4000);
    });
    return true;
  } catch {
    return false;
  }
}

async function maximizeWorkspaceBrowserWindow() {
  const debugPort = Number(desktopWorkspaceBrowserSession.debugPort || 0);
  if (!debugPort || typeof WebSocket !== 'function') return false;
  try {
    const response = await fetch(`http://127.0.0.1:${debugPort}/json/list`);
    if (!response.ok) return false;
    const targets = await response.json();
    const target = Array.isArray(targets)
      ? targets.find((candidate) => candidate?.webSocketDebuggerUrl && String(candidate.url || '').includes('web.whatsapp.com'))
        || targets.find((candidate) => candidate?.webSocketDebuggerUrl)
      : null;
    if (!target?.webSocketDebuggerUrl || !target?.id) return false;

    await new Promise((resolvePromise, rejectPromise) => {
      const socket = new WebSocket(target.webSocketDebuggerUrl);
      const cleanup = () => {
        try {
          socket.close();
        } catch {
          // Ignore close failures.
        }
      };
      socket.addEventListener('open', () => {
        socket.send(JSON.stringify({
          id: 1,
          method: 'Browser.getWindowForTarget',
          params: { targetId: target.id },
        }));
      });
      socket.addEventListener('message', (event) => {
        try {
          const payload = JSON.parse(String(event.data || '{}'));
          if (payload?.id === 1) {
            const windowId = Number(payload?.result?.windowId || 0);
            if (!windowId) {
              cleanup();
              resolvePromise(false);
              return;
            }
            socket.send(JSON.stringify({
              id: 2,
              method: 'Browser.setWindowBounds',
              params: {
                windowId,
                bounds: { windowState: 'maximized' },
              },
            }));
            return;
          }
          if (payload?.id === 2) {
            cleanup();
            resolvePromise(true);
          }
          if (payload?.error) {
            cleanup();
            rejectPromise(new Error('Unable to maximize browser window.'));
          }
        } catch {
          // Ignore parse noise from other events.
        }
      });
      socket.addEventListener('error', (error) => {
        cleanup();
        rejectPromise(error);
      });
      setTimeout(() => {
        cleanup();
        resolvePromise(false);
      }, 4000);
    });
    return true;
  } catch {
    return false;
  }
}

async function ensureWorkspaceBrowserTarget(target, availability, url, bounds) {
  const executable = target === 'edge' ? availability.paths.edge : availability.paths.chrome;
  if (!executable) return false;

  const targetProcessNames = target === 'edge' ? ['msedge'] : ['chrome'];
  const debugPort = WORKSPACE_BROWSER_DEBUG_PORTS[target];
  const profileDir = getWorkspaceBrowserProfileDir(target);
  const alignBrowser = async () => {
    const alignedByDebugger = bounds ? await setWorkspaceBrowserBounds(bounds) : true;
    if (bounds && !alignedByDebugger) {
      repositionExternalWindow(targetProcessNames, bounds, profileDir);
    } else if (!bounds) {
      await maximizeWorkspaceBrowserWindow();
    }
  };

  if (desktopWorkspaceBrowserSession.target === target && desktopWorkspaceBrowserSession.debugPort === debugPort) {
    for (let attempt = 0; attempt < 12; attempt += 1) {
      const navigated = await navigateWorkspaceBrowserSession(url);
      if (navigated) {
        await alignBrowser();
        return true;
      }
      if (processWindowExists(targetProcessNames, profileDir)) {
        await delay(350);
        continue;
      }
      break;
    }
  }

  if (processWindowExists(targetProcessNames, profileDir)) {
    desktopWorkspaceBrowserSession = {
      target,
      debugPort,
      profileDir,
      processNames: targetProcessNames,
    };
    for (let attempt = 0; attempt < 10; attempt += 1) {
      await delay(350);
      const navigated = await navigateWorkspaceBrowserSession(url);
      if (navigated) {
        await alignBrowser();
        return true;
      }
    }
    if (processWindowExists(targetProcessNames, profileDir)) {
      await alignBrowser();
      return true;
    }
  }

  closeWorkspaceBrowserProcesses(targetProcessNames, profileDir);
  await delay(250);

  const args = [
    '--new-window',
    `--remote-debugging-port=${debugPort}`,
    `--user-data-dir=${profileDir}`,
    '--disable-session-crashed-bubble',
    '--no-first-run',
    '--no-default-browser-check',
    `--app=${url}`,
  ];
  if (bounds) {
    args.splice(args.length - 1, 0, `--window-position=${bounds.x},${bounds.y}`, `--window-size=${bounds.width},${bounds.height}`);
  } else {
    args.splice(args.length - 1, 0, '--start-maximized');
  }
  launchGuiProcess(executable, args);
  desktopWorkspaceBrowserSession = {
    target,
    debugPort,
    profileDir,
    processNames: targetProcessNames,
  };

  for (let attempt = 0; attempt < 12; attempt += 1) {
    await delay(400);
    const navigated = await navigateWorkspaceBrowserSession(url);
    if (navigated || processWindowExists(targetProcessNames, profileDir)) {
      await alignBrowser();
      return true;
    }
  }
  return false;
}

function resolvePreferredWorkspaceTarget(preference, availability) {
  if (desktopWorkspaceActive) return preference;
  for (const candidate of buildTargetChain(preference)) {
    if (candidate === 'chrome' && availability.chrome) return 'chrome';
    if (candidate === 'edge' && availability.edge) return 'edge';
    if (candidate === 'whatsapp_desktop' && availability.whatsapp_desktop) return 'whatsapp_desktop';
    if (candidate === 'default_browser' && availability.default_browser) return 'default_browser';
  }
  return preference;
}

async function openWorkspaceWhatsappDesktop(appUrl, availability, bounds) {
  const whatsappPath = String(availability.paths?.whatsapp_desktop || resolveWhatsappDesktopExecutable()).trim();
  if (!availability.whatsapp_desktop) {
    return {
      success: false,
      target: 'whatsapp_desktop',
      label: TARGET_LABELS.whatsapp_desktop,
      availability,
      error: 'WhatsApp Desktop is not installed on this device.',
    };
  }

  const bootstrapUri = appUrl || 'whatsapp://send';
  let launched = false;
  if (appUrl) {
    launched = Boolean(whatsappPath) && launchWindowsExecutable(whatsappPath, [appUrl]);
    if (!launched && launchAppUserModelId(WHATSAPP_DESKTOP_APP_ID)) {
      await waitForExternalWindow(['WhatsApp.Root', 'ApplicationFrameHost', 'msedgewebview2'], '', 16, 200);
      launched = Boolean(whatsappPath) && launchWindowsExecutable(whatsappPath, [appUrl]);
    }
    if (!launched) {
      launched = launchWindowsUri(appUrl);
    }
  } else {
    launched = (Boolean(whatsappPath) && launchWindowsExecutable(whatsappPath, []))
      || launchAppUserModelId(WHATSAPP_DESKTOP_APP_ID)
      || launchWindowsUri(bootstrapUri);
  }

  if (!launched) {
    return {
      success: false,
      target: 'whatsapp_desktop',
      label: TARGET_LABELS.whatsapp_desktop,
      availability,
      error: 'WhatsApp Desktop could not be launched on this device.',
    };
  }

  await waitForExternalWindow(['WhatsApp.Root', 'ApplicationFrameHost', 'msedgewebview2']);
  if (bounds?.right && bounds?.left) {
    moveMainWindowToBounds(bounds.right);
    repositionExternalWindow(['WhatsApp.Root', 'ApplicationFrameHost', 'msedgewebview2'], bounds.left);
    await delay(450);
    repositionExternalWindow(['WhatsApp.Root', 'ApplicationFrameHost', 'msedgewebview2'], bounds.left);
  } else {
    maximizeExternalWindow(['WhatsApp.Root', 'ApplicationFrameHost', 'msedgewebview2']);
  }

  return {
    success: true,
    target: 'whatsapp_desktop',
    label: TARGET_LABELS.whatsapp_desktop,
    availability,
  };
}

async function openExternalSendTarget(payload) {
  const preference = normalizeDesktopTarget(payload?.preference);
  const webUrl = String(payload?.webUrl || '').trim();
  const appUrl = String(payload?.appUrl || '').trim();
  const availability = getAvailableSendTargets();
  const workspaceBounds = desktopWorkspaceActive && preference !== 'whatsapp_desktop' ? getDesktopWorkspaceBounds() : null;
  const reuseBrowserSession = Boolean(payload?.reuseBrowserSession);

  if (desktopWorkspaceActive) {
    if (preference === 'whatsapp_desktop') {
      return openWorkspaceWhatsappDesktop(appUrl, availability, workspaceBounds);
    }
    try {
      await loadDesktopWhatsappTarget(webUrl || EMBEDDED_WHATSAPP_URL);
      return {
        success: true,
        target: preference,
        label: EMBEDDED_WHATSAPP_LABEL,
        availability,
      };
    } catch (error) {
      return {
        success: false,
        target: preference,
        label: EMBEDDED_WHATSAPP_LABEL,
        availability,
        error: error instanceof Error ? error.message : 'The embedded WhatsApp workspace could not be loaded.',
      };
    }
  }

  const targetChain = reuseBrowserSession ? ['chrome', 'edge'] : buildTargetChain(preference);
  for (const target of targetChain) {
    try {
      if (target === 'whatsapp_desktop') {
        if (!appUrl || !availability.whatsapp_desktop) continue;
        const whatsappPath = String(availability.paths?.whatsapp_desktop || resolveWhatsappDesktopExecutable()).trim();
        let opened = Boolean(whatsappPath) && launchWindowsExecutable(whatsappPath, [appUrl]);
        if (!opened && launchAppUserModelId(WHATSAPP_DESKTOP_APP_ID)) {
          opened = launchWindowsUri(appUrl);
        }
        if (!opened) {
          opened = launchWindowsUri(appUrl);
        }
        if (!opened) continue;
        await waitForExternalWindow(['WhatsApp.Root', 'ApplicationFrameHost', 'msedgewebview2']);
        maximizeExternalWindow(['WhatsApp.Root', 'ApplicationFrameHost', 'msedgewebview2']);
        return { success: true, target, label: TARGET_LABELS[target], availability };
      }
      if (target === 'chrome') {
        if (!webUrl || !availability.paths.chrome) continue;
        if (workspaceBounds || reuseBrowserSession) {
          if (workspaceBounds?.right) moveMainWindowToBounds(workspaceBounds.right);
          const opened = await ensureWorkspaceBrowserTarget('chrome', availability, webUrl, workspaceBounds?.left || null);
          if (!opened) continue;
        } else {
          launchGuiProcess(availability.paths.chrome, [webUrl]);
        }
        return { success: true, target, label: TARGET_LABELS[target], availability };
      }
      if (target === 'edge') {
        if (!webUrl || !availability.paths.edge) continue;
        if (workspaceBounds || reuseBrowserSession) {
          if (workspaceBounds?.right) moveMainWindowToBounds(workspaceBounds.right);
          const opened = await ensureWorkspaceBrowserTarget('edge', availability, webUrl, workspaceBounds?.left || null);
          if (!opened) continue;
        } else {
          launchGuiProcess(availability.paths.edge, [webUrl]);
        }
        return { success: true, target, label: TARGET_LABELS[target], availability };
      }
      if (target === 'default_browser') {
        if (!webUrl) continue;
        await shell.openExternal(webUrl);
        return { success: true, target, label: TARGET_LABELS[target], availability };
      }
    } catch {
      // Try the next target fallback.
    }
  }

  return {
    success: false,
    target: preference,
    label: TARGET_LABELS[preference],
    availability,
    error: 'No supported external send target could be launched on this device.',
  };
}

function getDesktopWorkspaceState(preference = 'default_browser') {
  const normalizedPreference = normalizeDesktopTarget(preference);
  const availability = getAvailableSendTargets();
  const effectiveTarget = resolvePreferredWorkspaceTarget(normalizedPreference, availability);
  return {
    supported: true,
    active: desktopWorkspaceActive,
    loading: desktopWhatsappViewLoading,
    preferredTarget: effectiveTarget,
    preferredTargetLabel: desktopWorkspaceActive && effectiveTarget !== 'whatsapp_desktop'
      ? EMBEDDED_WHATSAPP_LABEL
      : TARGET_LABELS[effectiveTarget],
    availableTargets: availability,
    error: '',
  };
}

function enterDesktopSendWorkspace(preference = 'default_browser') {
  if (!mainWindowRef) {
    return {
      ...getDesktopWorkspaceState(preference),
      active: false,
      error: 'Desktop workspace window is not available.',
    };
  }

  if (!desktopWorkspaceRestoreBounds) {
    desktopWorkspaceRestoreBounds = mainWindowRef.getBounds();
  }

  mainWindowRef.setMinimumSize(DESKTOP_WORKSPACE_MIN_WIDTH, DESKTOP_WORKSPACE_MIN_HEIGHT);
  maximizeMainWindow();
  mainWindowRef.show();
  mainWindowRef.focus();
  desktopWorkspaceActive = true;
  const workspaceBounds = getDesktopWorkspaceBounds();
  if (preference === 'whatsapp_desktop') {
    maximizeMainWindow();
    collapseEmbeddedWhatsappView();
    detachDesktopWhatsappView();
  } else {
    attachDesktopWhatsappView();
    syncEmbeddedWhatsappBounds();
  }
  return getDesktopWorkspaceState(preference);
}

function showDesktopSendWorkspace(preference = 'default_browser') {
  if (!mainWindowRef) {
    return {
      ...getDesktopWorkspaceState(preference),
      active: false,
      error: 'Desktop workspace window is not available.',
    };
  }
  maximizeMainWindow();
  mainWindowRef.show();
  mainWindowRef.focus();
  desktopWorkspaceActive = true;
  const workspaceBounds = getDesktopWorkspaceBounds();
  if (preference === 'whatsapp_desktop') {
    maximizeMainWindow();
    collapseEmbeddedWhatsappView();
    detachDesktopWhatsappView();
  } else {
    attachDesktopWhatsappView();
    syncEmbeddedWhatsappBounds();
  }
  return getDesktopWorkspaceState(preference);
}

async function hideDesktopSendWorkspace(preference = 'default_browser') {
  maximizeMainWindow();
  await fadeOutDesktopWhatsappView(190);
  desktopWorkspaceActive = false;
  desktopWhatsappViewLoading = false;
  collapseEmbeddedWhatsappView();
  return getDesktopWorkspaceState(preference);
}

async function hideDesktopSendWorkspaceAnimated(preference = 'default_browser') {
  if (!mainWindowRef || !desktopWhatsappView) {
    return hideDesktopSendWorkspace(preference);
  }

  maximizeMainWindow();
  const initialBounds = getEmbeddedWhatsappBounds();
  if (!initialBounds || initialBounds.width <= 0 || initialBounds.height <= 0) {
    return hideDesktopSendWorkspace(preference);
  }

  const startTime = Date.now();
  const durationMs = 340;
  if (typeof desktopWhatsappView.setAutoResize === 'function') {
    desktopWhatsappView.setAutoResize({ width: false, height: false });
  }

  while (true) {
    const elapsed = Date.now() - startTime;
    const progress = Math.min(1, elapsed / durationMs);
    const eased = progress < 0.5
      ? 4 * progress * progress * progress
      : 1 - Math.pow(-2 * progress + 2, 3) / 2;
    const offsetY = Math.round(initialBounds.height * eased);
    const nextHeight = Math.max(0, initialBounds.height - offsetY);

    desktopWhatsappView.setBounds({
      x: initialBounds.x,
      y: initialBounds.y + offsetY,
      width: initialBounds.width,
      height: nextHeight,
    });

    if (progress >= 1) break;
    await delay(12);
  }

  desktopWorkspaceActive = false;
  desktopWhatsappViewLoading = false;
  collapseEmbeddedWhatsappView();
  return getDesktopWorkspaceState(preference);
}

function exitDesktopSendWorkspace(preference = 'default_browser') {
  detachDesktopWhatsappView();
  closeFloatingSendWindow('exit');
  desktopWhatsappViewLoading = false;
  if (mainWindowRef) {
    mainWindowRef.setMinimumSize(DEFAULT_MAIN_MIN_WIDTH, DEFAULT_MAIN_MIN_HEIGHT);
    maximizeMainWindow();
  }
  desktopWorkspaceRestoreBounds = null;
  desktopWorkspaceActive = false;
  desktopWorkspaceBrowserSession = {
    target: desktopWorkspaceBrowserSession.target,
    debugPort: desktopWorkspaceBrowserSession.debugPort,
    profileDir: desktopWorkspaceBrowserSession.profileDir,
    processNames: desktopWorkspaceBrowserSession.processNames,
  };
  return getDesktopWorkspaceState(preference);
}

async function createMainWindow() {
  lastConnectivityState = await resolveServerOriginWithLocator();
  process.env.SHINE_DESKTOP_API_ORIGIN = apiOrigin;

  const windowRef = new BrowserWindow({
    width: 1440,
    height: 900,
    minWidth: 1180,
    minHeight: 760,
    autoHideMenuBar: true,
    backgroundColor: '#0b1220',
    show: false,
    title: 'RMKCET Shine',
    icon: getDesktopIconPath('window') || undefined,
      webPreferences: {
        contextIsolation: true,
        nodeIntegration: false,
        backgroundThrottling: false,
        preload: resolve(currentDir, 'preload.cjs'),
      },
  });
  mainWindowRef = windowRef;

  let rendererTarget = devRendererUrl;
  if (desktopMode === 'desktop-app') {
    rendererTarget = await startDesktopShellServer();
  }

  if (lastConnectivityState.online) {
    await waitForRenderer(`${apiOrigin}/api/bootstrap`);
  }
  if (desktopMode === 'desktop-dev') {
    await waitForRenderer(devRendererUrl);
  }

  attachExternalNavigationGuards(windowRef.webContents, rendererTarget);
  const startupUpdate = await runStartupUpdateGate();
  if (startupUpdate.installing) return;

  if (lastConnectivityState.online) {
    await windowRef.loadURL(rendererTarget);
  } else {
    await showNoInternetPage();
  }
  const startHidden = process.argv.includes('--hidden') && desktopSettings.startMinimizedToTrayOnLogin;
  if (!startHidden) {
    windowRef.show();
    maximizeMainWindow();
  }

  windowRef.on('resize', () => {
    syncEmbeddedWhatsappBounds();
  });

  windowRef.on('close', (event) => {
    if (appIsQuitting || !desktopSettings.minimizeToTrayOnClose) return;
    event.preventDefault();
    windowRef.hide();
  });

  windowRef.on('closed', () => {
    if (floatingSendWindow && !floatingSendWindow.isDestroyed()) {
      floatingSendWindow.close();
    }
    detachDesktopWhatsappView();
    if (desktopWhatsappView && !desktopWhatsappView.webContents.isDestroyed()) {
      try {
        desktopWhatsappView.webContents.close();
      } catch {
        // Ignore close failures during shutdown.
      }
    }
    desktopWhatsappView = null;
    desktopWhatsappViewLoading = false;
    mainWindowRef = null;
    desktopWorkspaceRestoreBounds = null;
    desktopWorkspaceActive = false;
  });
}

ipcMain.handle('shine:openExternal', async (_event, url) => {
  const safeUrl = String(url || '').trim();
  if (!safeUrl) return false;
  if (/^whatsapp:\/\//i.test(safeUrl)) {
    const whatsappPath = resolveWhatsappDesktopExecutable();
    if (whatsappPath && launchWindowsExecutable(whatsappPath, [safeUrl])) {
      return true;
    }
    if (launchAppUserModelId(WHATSAPP_DESKTOP_APP_ID) && launchWindowsUri(safeUrl)) {
      return true;
    }
    if (launchWindowsUri(safeUrl)) {
      return true;
    }
    return false;
  }
  await shell.openExternal(safeUrl);
  return true;
});

ipcMain.handle('shine:desktopSendWorkspace:getTargets', async () => getAvailableSendTargets());
ipcMain.handle('shine:desktopSendWorkspace:enter', async (_event, preference) => enterDesktopSendWorkspace(preference));
ipcMain.handle('shine:desktopSendWorkspace:show', async (_event, preference) => showDesktopSendWorkspace(preference));
ipcMain.handle('shine:desktopSendWorkspace:hide', async (_event, preference) => hideDesktopSendWorkspace(preference));
ipcMain.handle('shine:desktopSendWorkspace:hideAnimated', async (_event, preference) => hideDesktopSendWorkspaceAnimated(preference));
ipcMain.handle('shine:desktopSendWorkspace:exit', async (_event, preference) => exitDesktopSendWorkspace(preference));
ipcMain.handle('shine:desktopSendWorkspace:state', async (_event, preference) => getDesktopWorkspaceState(preference));
ipcMain.handle('shine:desktopSendWorkspace:openTarget', async (_event, payload) => openExternalSendTarget(payload));
ipcMain.handle('shine:floatingSend:show', async (_event, payload) => showFloatingSendWindow(payload));
ipcMain.handle('shine:floatingSend:close', async (_event, reason) => closeFloatingSendWindow(reason));
ipcMain.handle('shine:floatingSend:pick', async (_event, regNo) => {
  const safeRegNo = String(regNo || '').trim();
  if (!safeRegNo || !mainWindowRef || mainWindowRef.isDestroyed()) return false;
  mainWindowRef.webContents.send('shine:floatingSend:pick', {
    kind: floatingSendPayload?.kind === 'notice' ? 'notice' : 'report',
    regNo: safeRegNo,
  });
  keepFloatingSendWindowOnTop();
  return true;
});
ipcMain.handle('shine:desktopSettings:get', async () => desktopSettings);
ipcMain.handle('shine:desktopSettings:save', async (_event, patch) => {
  const safePatch = patch && typeof patch === 'object' ? patch : {};
  desktopSettings = await writeDesktopSettings(enforceDesktopSettingsForRole({
    ...desktopSettings,
    ...safePatch,
  }, safePatch.role));
  return desktopSettings;
});
ipcMain.handle('shine:desktopConnectivity:get', async () => lastConnectivityState);
ipcMain.handle('shine:desktopConnectivity:retry', async () => {
  lastConnectivityState = await resolveServerOriginWithLocator();
  process.env.SHINE_DESKTOP_API_ORIGIN = apiOrigin;
  if (mainWindowRef && !mainWindowRef.isDestroyed()) {
    if (lastConnectivityState.online) {
      const rendererTarget = desktopMode === 'desktop-app' ? shellOrigin : devRendererUrl;
      await mainWindowRef.loadURL(rendererTarget);
    } else {
      await showNoInternetPage();
    }
    restoreMainWindow();
  }
  return lastConnectivityState;
});
ipcMain.handle('shine:desktopUpdate:check', async () => checkDesktopUpdate({ interactive: true }));
ipcMain.handle('shine:desktopUpdate:install', async () => installDesktopUpdate());
ipcMain.handle('shine:desktopNotification:show', async (_event, payload) => showDesktopNotification(payload));
ipcMain.handle('shine:desktopSettings:open', async () => {
  openDesktopSettings();
  return true;
});

app.on('window-all-closed', () => {
  if (appIsQuitting && process.platform !== 'darwin') app.quit();
});

app.on('before-quit', async () => {
  appIsQuitting = true;
  if (desktopUpdateCheckTimer) {
    clearInterval(desktopUpdateCheckTimer);
    desktopUpdateCheckTimer = null;
  }
  if (!shellServer) return;
  await new Promise((resolvePromise) => shellServer.close(() => resolvePromise()));
  shellServer = null;
});

app.on('second-instance', () => {
  restoreMainWindow();
});

app.whenReady().then(async () => {
  app.setName('RMKCET Shine');
  process.env.SHINE_DESKTOP_APP_VERSION = String(app.getVersion() || '').trim() || '0.1.0';
  applyLoginItemSettings();
  logDesktopIconDiagnostics();
  refreshWindowsShortcutIcons();
  createTray();
  try {
    await createMainWindow();
    scheduleDesktopUpdateChecks();
    if (desktopSettings.updateChecksEnabled) {
      setTimeout(() => void checkDesktopUpdate(), 4500);
    }
  } catch (error) {
    const failureWindow = new BrowserWindow({
      width: 980,
      height: 720,
      autoHideMenuBar: true,
      backgroundColor: '#0b1220',
      title: 'RMKCET Shine - Desktop Launch Error',
      webPreferences: {
        contextIsolation: true,
        nodeIntegration: false,
      },
    });
    const message = error instanceof Error ? error.message : 'Unknown desktop launch error.';
    await failureWindow.loadURL(`data:text/html,${encodeURIComponent(`<!doctype html><html><head><meta charset="utf-8"><title>RMKCET Shine</title><style>body{font-family:Segoe UI,system-ui,sans-serif;background:#0b1220;color:#e6edf8;display:grid;place-items:center;min-height:100vh;margin:0}main{max-width:760px;padding:32px;border:1px solid rgba(148,163,184,.28);border-radius:24px;background:rgba(15,23,42,.88);box-shadow:0 30px 80px rgba(2,6,23,.45)}h1{margin:0 0 12px;font-size:1.6rem}p{margin:0 0 12px;color:#bdd0f4;line-height:1.5}code{background:rgba(15,23,42,.75);padding:2px 8px;border-radius:999px}</style></head><body><main><h1>Desktop shell could not start</h1><p>${message}</p><p>Mode: <code>${desktopMode}</code></p><p>Expected API origin: <code>${apiOrigin}</code></p><p>Renderer origin: <code>${desktopMode === 'desktop-app' ? shellOrigin : devRendererUrl}</code></p></main></body></html>`)}`);
  }
});

app.on('activate', async () => {
  if (mainWindowRef && !mainWindowRef.isDestroyed()) {
    restoreMainWindow();
    return;
  }
  await createMainWindow();
});

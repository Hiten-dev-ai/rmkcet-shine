export type ShineRuntimeMode = 'web' | 'desktop-dev' | 'desktop-app';
export type DesktopSendTargetPreference = 'default_browser' | 'chrome' | 'edge' | 'whatsapp_desktop';

export type DesktopSendTargetAvailability = {
  default_browser: boolean;
  chrome: boolean;
  edge: boolean;
  whatsapp_desktop: boolean;
  paths?: Partial<Record<'chrome' | 'edge' | 'whatsapp_desktop', string>>;
};

export type DesktopSendWorkspaceState = {
  supported: boolean;
  active: boolean;
  loading: boolean;
  preferredTarget: DesktopSendTargetPreference;
  preferredTargetLabel: string;
  availableTargets: DesktopSendTargetAvailability;
  error: string;
};

export type DesktopAppSettings = {
  launchAtWindowsStartup: boolean;
  startMinimizedToTrayOnLogin: boolean;
  minimizeToTrayOnClose: boolean;
  desktopNotificationsEnabled: boolean;
  updateChecksEnabled: boolean;
  autoInstallUpdatesWhenIdle: boolean;
  notificationPollMinutes: number;
  currentServerOriginOverride: string;
  locatorCsvUrl: string;
  releaseChannelBaseUrl: string;
  higherOfficialDigestDay: string;
  higherOfficialDigestScope: 'all' | 'allocated';
};

export type DesktopConnectivityState = {
  online: boolean;
  apiOrigin: string;
  source: string;
  locator?: Record<string, string> | null;
  error?: string;
};

export type DesktopUpdateInfo = {
  available: boolean;
  currentVersion?: string;
  version?: string;
  manifestUrl?: string;
  exeUrl?: string;
  error?: string;
  skipped?: boolean;
  reason?: string;
  releaseNotes?: string[];
};

type DesktopBridge = {
  mode: Exclude<ShineRuntimeMode, 'web'>;
  appVersion: string;
  shellOrigin: string;
  apiOrigin: string;
  featureFlags?: {
    googleLoginSupported?: boolean;
    desktopSendWorkspaceSupported?: boolean;
  };
  openExternal?: (url: string) => Promise<boolean> | boolean;
  getDesktopAppSettings?: () => Promise<DesktopAppSettings> | DesktopAppSettings;
  saveDesktopAppSettings?: (patch: Partial<DesktopAppSettings>) => Promise<DesktopAppSettings> | DesktopAppSettings;
  getDesktopConnectivityState?: () => Promise<DesktopConnectivityState> | DesktopConnectivityState;
  retryDesktopConnectivity?: () => Promise<DesktopConnectivityState> | DesktopConnectivityState;
  checkDesktopUpdate?: () => Promise<DesktopUpdateInfo> | DesktopUpdateInfo;
  installDesktopUpdate?: () => Promise<{ success: boolean; error?: string; deferred?: boolean }> | { success: boolean; error?: string; deferred?: boolean };
  showDesktopNotification?: (payload: { title?: string; body?: string; message?: string; silent?: boolean }) => Promise<boolean> | boolean;
  openDesktopSettings?: () => Promise<boolean> | boolean;
  onOpenDesktopSettings?: (callback: () => void) => () => void;
  getAvailableSendTargets?: () => Promise<DesktopSendTargetAvailability> | DesktopSendTargetAvailability;
  enterDesktopSendWorkspace?: (preference?: DesktopSendTargetPreference) => Promise<DesktopSendWorkspaceState> | DesktopSendWorkspaceState;
  showDesktopSendWorkspace?: (preference?: DesktopSendTargetPreference) => Promise<DesktopSendWorkspaceState> | DesktopSendWorkspaceState;
  hideDesktopSendWorkspace?: (preference?: DesktopSendTargetPreference) => Promise<DesktopSendWorkspaceState> | DesktopSendWorkspaceState;
  hideDesktopSendWorkspaceAnimated?: (preference?: DesktopSendTargetPreference) => Promise<DesktopSendWorkspaceState> | DesktopSendWorkspaceState;
  exitDesktopSendWorkspace?: (preference?: DesktopSendTargetPreference) => Promise<DesktopSendWorkspaceState> | DesktopSendWorkspaceState;
  getDesktopSendWorkspaceState?: (preference?: DesktopSendTargetPreference) => Promise<DesktopSendWorkspaceState> | DesktopSendWorkspaceState;
  openExternalSendTarget?: (payload: {
    preference?: DesktopSendTargetPreference;
    webUrl?: string;
    appUrl?: string;
    reuseBrowserSession?: boolean;
  }) => Promise<{
    success: boolean;
    target: DesktopSendTargetPreference;
    label: string;
    availability: DesktopSendTargetAvailability;
    error?: string;
  }> | {
    success: boolean;
    target: DesktopSendTargetPreference;
    label: string;
    availability: DesktopSendTargetAvailability;
    error?: string;
  };
  showFloatingSendWindow?: (payload: FloatingSendWindowPayload) => Promise<{ success: boolean; error?: string }> | { success: boolean; error?: string };
  closeFloatingSendWindow?: (reason?: string) => Promise<{ success: boolean }> | { success: boolean };
  onFloatingSendRequest?: (callback: (payload: { kind?: 'report' | 'notice'; regNo?: string }) => void) => () => void;
  onFloatingSendClosed?: (callback: (payload: { reason?: string }) => void) => () => void;
};

export type FloatingSendWindowPayload = {
  kind: 'report' | 'notice';
  mode?: 'app' | 'web' | 'embed';
  title: string;
  subtitle?: string;
  theme?: 'light' | 'dark';
  themeVars?: Partial<Record<
    | 'primary'
    | 'primaryDark'
    | 'secondary'
    | 'accent'
    | 'success'
    | 'warning'
    | 'danger'
    | 'info'
    | 'bgPrimary'
    | 'bgSecondary'
    | 'bgCard'
    | 'text'
    | 'textDim'
    | 'textMuted'
    | 'border',
    string
  >>;
  rows: Array<{
    regNo: string;
    studentName: string;
    parentPhone?: string;
    status?: string;
    queueState?: string;
    active?: boolean;
    loading?: boolean;
  }>;
};

declare global {
  interface Window {
    __SHINE_DESKTOP__?: DesktopBridge;
  }
}

const LAST_AUTH_STATE_KEY = 'shine_last_auth_state';

function readDesktopBridge(): DesktopBridge | null {
  if (typeof window === 'undefined') return null;
  const candidate = window.__SHINE_DESKTOP__;
  if (!candidate || typeof candidate !== 'object') return null;
  return candidate;
}

function getWindowOrigin() {
  if (typeof window === 'undefined') return '';
  return String(window.location.origin || '').trim();
}

function isDesktopShellOrigin(hostname: string, port: string) {
  const normalizedHost = String(hostname || '').trim().replace(/^\[|\]$/g, '');
  const safePort = String(port || '').trim();
  return (normalizedHost === 'localhost' || normalizedHost === '127.0.0.1' || normalizedHost === '::1')
    && safePort === '5123';
}

function inferShellDesktopMode(): ShineRuntimeMode {
  if (typeof window === 'undefined') return 'web';
  return isDesktopShellOrigin(window.location.hostname, window.location.port) ? 'desktop-app' : 'web';
}

function inferDirectServerOrigin() {
  if (typeof window === 'undefined') return '';
  const rawHost = String(window.location.hostname || '').trim().replace(/^\[|\]$/g, '');
  const isLocalHost = rawHost === 'localhost' || rawHost === '127.0.0.1' || rawHost === '::1';
  if (!isLocalHost) return '';
  if (window.location.port !== '5000' && window.location.port !== '5123') return '';
  const host = rawHost.includes(':') ? `[${rawHost}]` : rawHost;
  return `${window.location.protocol}//${host}:5001`;
}

export const runtimeConfig = (() => {
  const bridge = readDesktopBridge();
  const mode = bridge?.mode || inferShellDesktopMode();
  const shellOrigin = String(bridge?.shellOrigin || getWindowOrigin()).trim();
  const directServerOrigin = String(bridge?.apiOrigin || inferDirectServerOrigin()).trim();
  return {
    mode,
    appOrigin: shellOrigin,
    apiBase: '',
    directServerOrigin,
    isDesktop: mode !== 'web',
    isDesktopDev: mode === 'desktop-dev',
    isDesktopApp: mode === 'desktop-app',
    appVersion: String(bridge?.appVersion || '').trim(),
    featureFlags: {
      googleLoginSupported: Boolean(bridge?.featureFlags?.googleLoginSupported),
      desktopSendWorkspaceSupported: Boolean(bridge?.featureFlags?.desktopSendWorkspaceSupported),
      canOpenExternal: typeof bridge?.openExternal === 'function',
    },
  } as const;
})();

export function resolveDirectServerUrl(path: string) {
  const safePath = String(path || '').trim();
  if (!safePath) return safePath;
  if (!runtimeConfig.directServerOrigin) return safePath;
  return `${runtimeConfig.directServerOrigin}${safePath}`;
}

export function clearStoredAuthState() {
  if (typeof window === 'undefined') return;
  try {
    window.localStorage.removeItem(LAST_AUTH_STATE_KEY);
    window.sessionStorage.removeItem(LAST_AUTH_STATE_KEY);
  } catch {
    // Ignore storage cleanup failures.
  }
}

export function reloadCurrentApp() {
  if (typeof window === 'undefined') return;
  window.location.reload();
}

export function redirectToAppRoot() {
  if (typeof window === 'undefined') return;
  window.location.assign('/');
}

export function openExternalLink(url: string) {
  const safeUrl = String(url || '').trim();
  if (!safeUrl || typeof window === 'undefined') return false;

  const bridge = readDesktopBridge();
  if (bridge?.openExternal) {
    void Promise.resolve(bridge.openExternal(safeUrl)).catch(() => {
      try {
        window.location.assign(safeUrl);
      } catch {
        // Ignore fallback navigation failures.
      }
    });
    return true;
  }

  try {
    window.location.assign(safeUrl);
    return true;
  } catch {
    return false;
  }
}

export async function getDesktopAppSettings(): Promise<DesktopAppSettings | null> {
  const bridge = readDesktopBridge();
  if (!bridge?.getDesktopAppSettings) return null;
  return Promise.resolve(bridge.getDesktopAppSettings());
}

export async function saveDesktopAppSettings(patch: Partial<DesktopAppSettings>): Promise<DesktopAppSettings | null> {
  const bridge = readDesktopBridge();
  if (!bridge?.saveDesktopAppSettings) return null;
  return Promise.resolve(bridge.saveDesktopAppSettings(patch));
}

export async function getDesktopConnectivityState(): Promise<DesktopConnectivityState | null> {
  const bridge = readDesktopBridge();
  if (!bridge?.getDesktopConnectivityState) return null;
  return Promise.resolve(bridge.getDesktopConnectivityState());
}

export async function retryDesktopConnectivity(): Promise<DesktopConnectivityState | null> {
  const bridge = readDesktopBridge();
  if (!bridge?.retryDesktopConnectivity) return null;
  return Promise.resolve(bridge.retryDesktopConnectivity());
}

export async function checkDesktopUpdate(): Promise<DesktopUpdateInfo | null> {
  const bridge = readDesktopBridge();
  if (!bridge?.checkDesktopUpdate) return null;
  return Promise.resolve(bridge.checkDesktopUpdate());
}

export async function installDesktopUpdate(): Promise<{ success: boolean; error?: string; deferred?: boolean } | null> {
  const bridge = readDesktopBridge();
  if (!bridge?.installDesktopUpdate) return null;
  return Promise.resolve(bridge.installDesktopUpdate());
}

export async function showDesktopNotification(payload: { title?: string; body?: string; message?: string; silent?: boolean }) {
  const bridge = readDesktopBridge();
  if (!bridge?.showDesktopNotification) return false;
  return Promise.resolve(bridge.showDesktopNotification(payload));
}

export function openDesktopSettings() {
  const bridge = readDesktopBridge();
  if (!bridge?.openDesktopSettings) return false;
  void Promise.resolve(bridge.openDesktopSettings());
  return true;
}

export function onOpenDesktopSettings(callback: () => void) {
  const bridge = readDesktopBridge();
  if (!bridge?.onOpenDesktopSettings) return () => {};
  return bridge.onOpenDesktopSettings(callback);
}

export async function getAvailableDesktopSendTargets(): Promise<DesktopSendTargetAvailability> {
  const bridge = readDesktopBridge();
  if (bridge?.getAvailableSendTargets) {
    return Promise.resolve(bridge.getAvailableSendTargets());
  }
  return {
    default_browser: true,
    chrome: false,
    edge: false,
    whatsapp_desktop: false,
  };
}

export async function enterDesktopSendWorkspace(preference: DesktopSendTargetPreference = 'default_browser'): Promise<DesktopSendWorkspaceState> {
  const bridge = readDesktopBridge();
  if (!bridge?.enterDesktopSendWorkspace) {
    return {
      supported: false,
      active: false,
      loading: false,
      preferredTarget: preference,
      preferredTargetLabel: 'Unavailable',
      availableTargets: await getAvailableDesktopSendTargets(),
      error: 'Desktop send workspace is not available in this runtime.',
    };
  }
  return Promise.resolve(bridge.enterDesktopSendWorkspace(preference));
}

export async function exitDesktopSendWorkspace(preference: DesktopSendTargetPreference = 'default_browser'): Promise<DesktopSendWorkspaceState> {
  const bridge = readDesktopBridge();
  if (!bridge?.exitDesktopSendWorkspace) {
    return {
      supported: false,
      active: false,
      loading: false,
      preferredTarget: preference,
      preferredTargetLabel: 'Unavailable',
      availableTargets: await getAvailableDesktopSendTargets(),
      error: 'Desktop send workspace is not available in this runtime.',
    };
  }
  return Promise.resolve(bridge.exitDesktopSendWorkspace(preference));
}

export async function showDesktopSendWorkspace(preference: DesktopSendTargetPreference = 'default_browser'): Promise<DesktopSendWorkspaceState> {
  const bridge = readDesktopBridge();
  if (!bridge?.showDesktopSendWorkspace) {
    return enterDesktopSendWorkspace(preference);
  }
  return Promise.resolve(bridge.showDesktopSendWorkspace(preference));
}

export async function hideDesktopSendWorkspace(preference: DesktopSendTargetPreference = 'default_browser'): Promise<DesktopSendWorkspaceState> {
  const bridge = readDesktopBridge();
  if (!bridge?.hideDesktopSendWorkspace) {
    return exitDesktopSendWorkspace(preference);
  }
  return Promise.resolve(bridge.hideDesktopSendWorkspace(preference));
}

export async function hideDesktopSendWorkspaceAnimated(preference: DesktopSendTargetPreference = 'default_browser'): Promise<DesktopSendWorkspaceState> {
  const bridge = readDesktopBridge();
  if (bridge?.hideDesktopSendWorkspaceAnimated) {
    return Promise.resolve(bridge.hideDesktopSendWorkspaceAnimated(preference));
  }
  return hideDesktopSendWorkspace(preference);
}

export async function getDesktopSendWorkspaceState(preference: DesktopSendTargetPreference = 'default_browser'): Promise<DesktopSendWorkspaceState> {
  const bridge = readDesktopBridge();
  if (!bridge?.getDesktopSendWorkspaceState) {
    return {
      supported: false,
      active: false,
      loading: false,
      preferredTarget: preference,
      preferredTargetLabel: 'Unavailable',
      availableTargets: await getAvailableDesktopSendTargets(),
      error: 'Desktop send workspace is not available in this runtime.',
    };
  }
  return Promise.resolve(bridge.getDesktopSendWorkspaceState(preference));
}

export async function openExternalSendTarget(payload: {
  preference?: DesktopSendTargetPreference;
  webUrl?: string;
  appUrl?: string;
  reuseBrowserSession?: boolean;
}) {
  const bridge = readDesktopBridge();
  if (!bridge?.openExternalSendTarget) {
    const fallbackUrl = String(payload.webUrl || payload.appUrl || '').trim();
    if (fallbackUrl) {
      openExternalLink(fallbackUrl);
      return {
        success: true,
        target: payload.preference || 'default_browser',
        label: 'External Target',
        availability: await getAvailableDesktopSendTargets(),
      };
    }
    return {
      success: false,
      target: payload.preference || 'default_browser',
      label: 'External Target',
      availability: await getAvailableDesktopSendTargets(),
      error: 'No external send target is available.',
    };
  }
  return Promise.resolve(bridge.openExternalSendTarget(payload));
}

export async function showFloatingSendWindow(payload: FloatingSendWindowPayload) {
  const bridge = readDesktopBridge();
  if (!bridge?.showFloatingSendWindow) return { success: false, error: 'Floating send window is unavailable.' };
  return Promise.resolve(bridge.showFloatingSendWindow(payload));
}

export async function closeFloatingSendWindow(reason = 'close') {
  const bridge = readDesktopBridge();
  if (!bridge?.closeFloatingSendWindow) return { success: false };
  return Promise.resolve(bridge.closeFloatingSendWindow(reason));
}

export function onFloatingSendRequest(callback: (payload: { kind?: 'report' | 'notice'; regNo?: string }) => void) {
  const bridge = readDesktopBridge();
  if (!bridge?.onFloatingSendRequest) return () => {};
  return bridge.onFloatingSendRequest(callback);
}

export function onFloatingSendClosed(callback: (payload: { reason?: string }) => void) {
  const bridge = readDesktopBridge();
  if (!bridge?.onFloatingSendClosed) return () => {};
  return bridge.onFloatingSendClosed(callback);
}

export function startGoogleOauth() {
  if (runtimeConfig.isDesktop) return false;
  try {
    window.location.assign('/auth/google/start');
    return true;
  } catch {
    return false;
  }
}

export {};

import { contextBridge, ipcRenderer } from 'electron';

const shellOrigin = String(process.env.SHINE_DESKTOP_SHELL_ORIGIN || '').trim();
const apiOrigin = String(process.env.SHINE_DESKTOP_API_ORIGIN || '').trim();
const mode = process.env.SHINE_DESKTOP_MODE === 'desktop-app' ? 'desktop-app' : 'desktop-dev';
const appVersion = String(process.env.npm_package_version || '0.1.0').trim() || '0.1.0';

contextBridge.exposeInMainWorld('__SHINE_DESKTOP__', {
  mode,
  appVersion,
  shellOrigin,
  apiOrigin,
  featureFlags: {
    googleLoginSupported: false,
    desktopSendWorkspaceSupported: true,
    localOauth: process.env.SHINE_DESKTOP_LOCAL_OAUTH === '1',
  },
  openExternal(url) {
    return ipcRenderer.invoke('shine:openExternal', url);
  },
  getDesktopAppSettings() {
    return ipcRenderer.invoke('shine:desktopSettings:get');
  },
  saveDesktopAppSettings(patch) {
    return ipcRenderer.invoke('shine:desktopSettings:save', patch);
  },
  getDesktopConnectivityState() {
    return ipcRenderer.invoke('shine:desktopConnectivity:get');
  },
  retryDesktopConnectivity() {
    return ipcRenderer.invoke('shine:desktopConnectivity:retry');
  },
  checkDesktopUpdate() {
    return ipcRenderer.invoke('shine:desktopUpdate:check');
  },
  installDesktopUpdate() {
    return ipcRenderer.invoke('shine:desktopUpdate:install');
  },
  showDesktopNotification(payload) {
    return ipcRenderer.invoke('shine:desktopNotification:show', payload);
  },
  openDesktopSettings() {
    return ipcRenderer.invoke('shine:desktopSettings:open');
  },
  onOpenDesktopSettings(callback) {
    if (typeof callback !== 'function') return () => {};
    const handler = () => callback();
    ipcRenderer.on('shine:desktopSettings:open', handler);
    return () => ipcRenderer.off('shine:desktopSettings:open', handler);
  },
  getAvailableSendTargets() {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:getTargets');
  },
  enterDesktopSendWorkspace(preference) {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:enter', preference);
  },
  showDesktopSendWorkspace(preference) {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:show', preference);
  },
  hideDesktopSendWorkspace(preference) {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:hide', preference);
  },
  hideDesktopSendWorkspaceAnimated(preference) {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:hideAnimated', preference);
  },
  exitDesktopSendWorkspace(preference) {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:exit', preference);
  },
  getDesktopSendWorkspaceState(preference) {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:state', preference);
  },
  openExternalSendTarget(payload) {
    return ipcRenderer.invoke('shine:desktopSendWorkspace:openTarget', payload);
  },
  showFloatingSendWindow(payload) {
    return ipcRenderer.invoke('shine:floatingSend:show', payload);
  },
  closeFloatingSendWindow(reason) {
    return ipcRenderer.invoke('shine:floatingSend:close', reason);
  },
  pickFloatingSendStudent(regNo) {
    return ipcRenderer.invoke('shine:floatingSend:pick', regNo);
  },
  onFloatingSendRequest(callback) {
    if (typeof callback !== 'function') return () => {};
    const handler = (_event, payload) => callback(payload);
    ipcRenderer.on('shine:floatingSend:pick', handler);
    return () => ipcRenderer.off('shine:floatingSend:pick', handler);
  },
  onFloatingSendClosed(callback) {
    if (typeof callback !== 'function') return () => {};
    const handler = (_event, payload) => callback(payload);
    ipcRenderer.on('shine:floatingSend:closed', handler);
    return () => ipcRenderer.off('shine:floatingSend:closed', handler);
  },
  onFloatingSendUpdate(callback) {
    if (typeof callback !== 'function') return () => {};
    const handler = (_event, payload) => callback(payload);
    ipcRenderer.on('shine:floatingSend:update', handler);
    return () => ipcRenderer.off('shine:floatingSend:update', handler);
  },
});

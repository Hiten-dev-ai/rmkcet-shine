import { spawn, spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { cp, mkdir, readdir, readFile, rm, stat, writeFile } from 'node:fs/promises';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const currentDir = dirname(fileURLToPath(import.meta.url));
export const desktopRoot = resolve(currentDir, '..');
export const repoRoot = resolve(desktopRoot, '..');
export const clientRoot = resolve(repoRoot, 'client');
export const clientDesktopDistRoot = resolve(clientRoot, 'dist-desktop');
export const runtimeDir = resolve(desktopRoot, 'runtime');
export const generatedRuntimeConfigPath = resolve(runtimeDir, 'release-config.json');
export const msixOutputRoot = resolve(desktopRoot, 'out', 'msix');
export const exeOutputRoot = resolve(desktopRoot, 'out', 'exe');
export const packagedOutputRoot = resolve(desktopRoot, 'out', 'packaged');
export const desktopInstallerRoot = resolve(repoRoot, 'data', 'desktop-installer');
export const desktopInstallerLatestRoot = resolve(desktopInstallerRoot, 'latest');
export const desktopInstallerReleasesRoot = resolve(desktopInstallerRoot, 'releases');
export const manifestTemplatePath = resolve(desktopRoot, 'Package.appxmanifest');
export const appInstallerTemplatePath = resolve(desktopRoot, 'appinstaller.template.xml');
export const desktopPackageJsonPath = resolve(desktopRoot, 'package.json');
export const rootPackageJsonPath = resolve(repoRoot, 'package.json');
export const desktopAssetSourcePath = resolve(repoRoot, 'client', 'assets', 'shine-logo-optimized.png');
export const desktopBuildFingerprintPath = resolve(desktopInstallerLatestRoot, 'build-fingerprint.json');

export async function readJson(filePath) {
  return JSON.parse(await readFile(filePath, 'utf8'));
}

async function hashFile(hash, filePath, relativePath) {
  hash.update(`file:${relativePath}\n`);
  hash.update(await readFile(filePath));
  hash.update('\n');
}

async function hashTree(hash, rootDir, prefix, ignored = new Set()) {
  const entries = await readdir(rootDir, { withFileTypes: true }).catch(() => []);
  entries.sort((left, right) => left.name.localeCompare(right.name));
  for (const entry of entries) {
    if (ignored.has(entry.name)) continue;
    const fullPath = resolve(rootDir, entry.name);
    const relativePath = `${prefix}/${entry.name}`.replace(/\\/g, '/');
    if (entry.isDirectory()) {
      await hashTree(hash, fullPath, relativePath, ignored);
    } else if (entry.isFile()) {
      await hashFile(hash, fullPath, relativePath);
    }
  }
}

export async function computeDesktopBuildFingerprint() {
  const hash = createHash('sha256');
  const ignored = new Set(['node_modules', 'dist', 'dist-desktop', 'dist-codex-check', 'dist-codex-check-2', 'out', '.workspace']);
  const inputs = [
    ['package.json', rootPackageJsonPath],
    ['client/package.json', resolve(clientRoot, 'package.json')],
    ['client/vite.config.ts', resolve(clientRoot, 'vite.config.ts')],
    ['desktop/package.json', desktopPackageJsonPath],
    ['desktop/runtime/release-config.json', generatedRuntimeConfigPath],
  ];
  for (const [label, filePath] of inputs) {
    if (existsSync(filePath)) await hashFile(hash, filePath, label);
  }
  for (const [label, dirPath] of [
    ['client/src', resolve(clientRoot, 'src')],
    ['client/assets', resolve(clientRoot, 'assets')],
    ['client/public', resolve(clientRoot, 'public')],
    ['desktop/src', resolve(desktopRoot, 'src')],
    ['desktop/assets', resolve(desktopRoot, 'assets')],
  ]) {
    if (existsSync(dirPath)) await hashTree(hash, dirPath, label, ignored);
  }
  return {
    schemaVersion: 1,
    version: getRootAppVersion(),
    hash: hash.digest('hex'),
  };
}

export async function ensureExists(filePath, label) {
  try {
    await stat(filePath);
  } catch {
    throw new Error(`${label} was not found at ${filePath}.`);
  }
}

export function getRootAppVersion() {
  if (!existsSync(rootPackageJsonPath)) return '0.1.0';
  try {
    const rootPackage = JSON.parse(readFileSync(rootPackageJsonPath, 'utf8'));
    return String(rootPackage.version || '0.1.0').trim() || '0.1.0';
  } catch {
    return '0.1.0';
  }
}

export function normalizeMsixVersion(version) {
  const raw = String(version || '').trim();
  const core = raw.split('-')[0];
  const parts = core.split('.').map((part) => {
    const digits = String(part || '').replace(/\D+/g, '');
    return digits ? Number(digits) : 0;
  });
  while (parts.length < 4) parts.push(0);
  return parts.slice(0, 4).join('.');
}

export function getDesktopArtifactBaseName(version) {
  return `RMKCET-Shine-${String(version || '').trim()}`;
}

export function getDesktopMsixFileName(version) {
  return `${getDesktopArtifactBaseName(version)}.msix`;
}

export function getDesktopExeFileName(version) {
  return `RMKCET-Shine-Setup-${String(version || '').trim()}.exe`;
}

export function getDesktopAppInstallerFileName() {
  return 'RMKCET-Shine.appinstaller';
}

export function getReleaseManifestFileName() {
  return 'release.json';
}

export function getEnvFlag(name, fallback = '') {
  return String(process.env[name] || fallback).trim();
}

export async function cleanDir(dirPath) {
  await rm(dirPath, { recursive: true, force: true }).catch(() => undefined);
  await mkdir(dirPath, { recursive: true });
}

export async function ensureDir(dirPath) {
  await mkdir(dirPath, { recursive: true });
}

export async function runCommand(command, args, options = {}) {
  const title = options.title ? `[desktop-release] ${options.title}` : `[desktop-release] ${command} ${args.join(' ')}`;
  console.log(title);
  const useShell = process.platform === 'win32' && /\.(cmd|bat)$/i.test(String(command || '').trim());
  await new Promise((resolvePromise, rejectPromise) => {
    const child = spawn(command, args, {
      cwd: options.cwd || repoRoot,
      stdio: 'inherit',
      env: {
        ...process.env,
        ...(options.env || {}),
      },
      shell: useShell,
    });
    child.on('error', rejectPromise);
    child.on('exit', (code, signal) => {
      if (signal) {
        rejectPromise(new Error(`${command} was interrupted by signal ${signal}.`));
        return;
      }
      if (code !== 0) {
        rejectPromise(new Error(`${command} exited with code ${code ?? 'unknown'}.`));
        return;
      }
      resolvePromise();
    });
  });
}

export function getNpmCommand() {
  return process.platform === 'win32' ? 'npm.cmd' : 'npm';
}

export function getWingetCommand() {
  return process.platform === 'win32' ? 'winget.exe' : 'winget';
}

export function verifyCommandAvailable(command, helpArgs = ['--version']) {
  const probe = spawnSync(command, helpArgs, {
    cwd: repoRoot,
    stdio: ['ignore', 'ignore', 'ignore'],
    shell: false,
    windowsHide: true,
  });
  return !probe.error && probe.status === 0;
}

export function ensureWinappInstalled() {
  const localPackagePath = resolve(desktopRoot, 'node_modules', '@microsoft', 'winappcli', 'package.json');
  if (existsSync(localPackagePath)) {
    const localCliPath = resolve(desktopRoot, 'node_modules', '@microsoft', 'winappcli', 'dist', 'cli.js');
    return {
      command: process.execPath,
      prefixArgs: [localCliPath],
    };
  }
  const systemCommand = process.platform === 'win32' ? 'winapp.exe' : 'winapp';
  if (!verifyCommandAvailable(systemCommand, ['--help'])) {
    throw new Error('WinApp CLI is not installed. Install the Electron-compatible package with `npm install --prefix desktop --save-dev @microsoft/winappcli`.');
  }
  return {
    command: systemCommand,
    prefixArgs: [],
  };
}

export async function writeRuntimeReleaseConfig() {
  const apiOrigin = getEnvFlag('SHINE_DESKTOP_RELEASE_API_ORIGIN', getEnvFlag('SERVER_ORIGIN', ''));
  if (!apiOrigin) {
    throw new Error('SHINE_DESKTOP_RELEASE_API_ORIGIN is required for desktop release packaging.');
  }
  await ensureDir(runtimeDir);
  await writeFile(generatedRuntimeConfigPath, JSON.stringify({
    apiOrigin,
    releaseChannelBaseUrl: getEnvFlag('SHINE_DESKTOP_RELEASE_CHANNEL_URL', ''),
    locatorCsvUrl: getEnvFlag('SHINE_DESKTOP_LOCATOR_CSV_URL', ''),
    downloadPageUrl: getEnvFlag('SHINE_DESKTOP_DOWNLOAD_PAGE_URL', ''),
  }, null, 2));
  return generatedRuntimeConfigPath;
}

export async function writeTemplatedFile(templatePath, targetPath, replacements) {
  let content = await readFile(templatePath, 'utf8');
  for (const [key, value] of Object.entries(replacements)) {
    content = content.replaceAll(`{{${key}}}`, String(value));
  }
  await ensureDir(dirname(targetPath));
  await writeFile(targetPath, content);
}

export function getReleaseNotesLines() {
  const inline = getEnvFlag('SHINE_DESKTOP_RELEASE_NOTES', '');
  if (inline) {
    return inline.split(/\r?\n/).map((line) => line.trim()).filter(Boolean);
  }
  return [];
}

export async function copyMsixAssets(targetAssetsDir) {
  await ensureExists(desktopAssetSourcePath, 'Desktop app logo asset');
  await ensureDir(targetAssetsDir);
  const assetNames = [
    'Square44x44Logo.png',
    'Square150x150Logo.png',
    'Wide310x150Logo.png',
    'StoreLogo.png',
  ];
  for (const fileName of assetNames) {
    await cp(desktopAssetSourcePath, resolve(targetAssetsDir, fileName), { force: true });
  }
}

export async function buildClientDesktopShellIfMissing() {
  if (existsSync(clientDesktopDistRoot)) return;
  await runCommand(getNpmCommand(), ['run', 'build:desktop-shell', '--prefix', 'client'], {
    cwd: repoRoot,
    title: 'Building desktop client shell',
  });
}

export async function readDesktopPackageJson() {
  return readJson(desktopPackageJsonPath);
}

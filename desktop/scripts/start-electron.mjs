import { spawn, spawnSync } from 'node:child_process';
import { access, mkdir, readdir, rm, writeFile } from 'node:fs/promises';
import { constants as fsConstants, existsSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { createRequire } from 'node:module';

const currentDir = dirname(fileURLToPath(import.meta.url));
const desktopRoot = resolve(currentDir, '..');
const modeArg = process.argv[2] === 'desktop-app' ? 'desktop-app' : 'desktop-dev';
const require = createRequire(import.meta.url);
const electronCli = resolve(desktopRoot, 'node_modules', 'electron', 'cli.js');
const electronInstallScript = resolve(desktopRoot, 'node_modules', 'electron', 'install.js');
const electronPackageJson = resolve(desktopRoot, 'node_modules', 'electron', 'package.json');
const electronDistDir = resolve(desktopRoot, 'node_modules', 'electron', 'dist');
const electronPathFile = resolve(desktopRoot, 'node_modules', 'electron', 'path.txt');
const electronBinaryDirect = resolve(electronDistDir, process.platform === 'win32' ? 'electron.exe' : 'electron');

async function ensureElectronCli() {
  try {
    await access(electronCli, fsConstants.R_OK);
  } catch {
    console.error('Electron is not installed for the desktop shell yet. Run `npm install --prefix desktop` first.');
    process.exit(1);
  }
}

function canResolveElectronBinary() {
  try {
    const electronBinary = require(resolve(desktopRoot, 'node_modules', 'electron'));
    return typeof electronBinary === 'string' && electronBinary.length > 0;
  } catch {
    return false;
  }
}

async function ensureElectronPathFileFromExistingBinary() {
  try {
    await access(electronBinaryDirect, fsConstants.R_OK);
  } catch {
    return false;
  }
  await writeFile(electronPathFile, process.platform === 'win32' ? 'electron.exe' : 'electron');
  return true;
}

async function locateCachedElectronZip() {
  const electronPackage = require(electronPackageJson);
  const version = String(electronPackage?.version || '').trim();
  if (!version) return null;

  const cacheRoot = resolve(process.env.LOCALAPPDATA || '', 'electron', 'Cache');
  try {
    const cacheEntries = await readdir(cacheRoot, { withFileTypes: true });
    const expectedZipName = `electron-v${version}-win32-x64.zip`;
    for (const entry of cacheEntries) {
      if (!entry.isDirectory()) continue;
      const zipPath = resolve(cacheRoot, entry.name, expectedZipName);
      try {
        await access(zipPath, fsConstants.R_OK);
        return zipPath;
      } catch {
        // Keep searching other cache directories.
      }
    }
  } catch {
    return null;
  }
  return null;
}

async function repairFromCachedZip() {
  const cachedZipPath = await locateCachedElectronZip();
  if (!cachedZipPath) return false;

  console.log(`[desktop] Using cached Electron package: ${cachedZipPath}`);
  await rm(electronDistDir, { recursive: true, force: true });
  await mkdir(electronDistDir, { recursive: true });
  const extraction = spawnSync('powershell.exe', [
    '-NoProfile',
    '-ExecutionPolicy',
    'Bypass',
    '-Command',
    `Expand-Archive -LiteralPath '${cachedZipPath.replace(/'/g, "''")}' -DestinationPath '${electronDistDir.replace(/'/g, "''")}' -Force`,
  ], {
    cwd: desktopRoot,
    stdio: 'inherit',
  });
  if (extraction.error) throw extraction.error;
  if (extraction.status !== 0) {
    throw new Error(`Electron cache extraction failed with exit code ${extraction.status ?? 'unknown'}.`);
  }
  await writeFile(electronPathFile, 'electron.exe');
  return canResolveElectronBinary();
}

async function repairElectronInstallIfNeeded() {
  if (canResolveElectronBinary()) return;
  if (await ensureElectronPathFileFromExistingBinary()) return;
  if (await repairFromCachedZip()) return;

  console.log('[desktop] Electron binary is missing or incomplete. Repairing local Electron install...');
  await new Promise((resolvePromise, rejectPromise) => {
    const repair = spawn(process.execPath, [electronInstallScript], {
      cwd: desktopRoot,
      stdio: 'inherit',
      env: {
        ...process.env,
      },
    });

    repair.on('exit', (code, signal) => {
      if (signal) {
        rejectPromise(new Error(`Electron install repair was interrupted by signal ${signal}.`));
        return;
      }
      if (code !== 0) {
        rejectPromise(new Error(`Electron install repair failed with exit code ${code ?? 'unknown'}.`));
        return;
      }
      resolvePromise();
    });
    repair.on('error', rejectPromise);
  });

  if (canResolveElectronBinary()) return;
  if (await ensureElectronPathFileFromExistingBinary()) return;
  if (!(await repairFromCachedZip())) {
    throw new Error('Electron install repair completed, but the Electron binary is still unavailable.');
  }
}

async function main() {
  await ensureElectronCli();
  await repairElectronInstallIfNeeded();
  const electronArgs = ['.'];
  if (process.platform === 'linux') {
    electronArgs.unshift('--disable-gpu');
    electronArgs.unshift('--no-sandbox');
  }
  const childEnv = {
    ...process.env,
    SHINE_DESKTOP_MODE: modeArg,
  };
  delete childEnv.ELECTRON_RUN_AS_NODE;
  const hasDisplay = Boolean(String(process.env.DISPLAY || process.env.WAYLAND_DISPLAY || '').trim());
  const xvfbRun = '/usr/bin/xvfb-run';
  const child = (
    process.platform === 'linux' && !hasDisplay && existsSync(xvfbRun)
      ? spawn(xvfbRun, ['-a', electronBinaryDirect, ...electronArgs], {
        cwd: desktopRoot,
        stdio: 'inherit',
        env: childEnv,
      })
      : spawn(electronBinaryDirect, electronArgs, {
        cwd: desktopRoot,
        stdio: 'inherit',
        env: childEnv,
      })
  );

  child.on('exit', (code, signal) => {
    if (signal) {
      process.kill(process.pid, signal);
      return;
    }
    process.exit(code ?? 0);
  });
}

void main();

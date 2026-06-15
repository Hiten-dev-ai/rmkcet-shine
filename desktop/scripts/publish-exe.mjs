import { cp, readdir, rm, stat, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import {
  cleanDir,
  computeDesktopBuildFingerprint,
  desktopBuildFingerprintPath,
  desktopInstallerLatestRoot,
  desktopInstallerReleasesRoot,
  ensureDir,
  ensureExists,
  exeOutputRoot,
  getDesktopExeFileName,
  getEnvFlag,
  getReleaseManifestFileName,
  getReleaseNotesLines,
  getRootAppVersion,
} from './release-utils.mjs';
import { runMakeExe } from './make-exe.mjs';

function buildBaseUrl() {
  const raw = getEnvFlag('SHINE_DESKTOP_PUBLIC_BASE_URL', '');
  if (!/^https?:\/\//i.test(raw)) {
    throw new Error('SHINE_DESKTOP_PUBLIC_BASE_URL is required for publishing desktop installer artifacts.');
  }
  return raw.replace(/\/+$/, '');
}

async function rotateOldReleaseFolders(keepCount = 5) {
  const entries = await readdir(desktopInstallerReleasesRoot, { withFileTypes: true }).catch(() => []);
  const folders = [];
  for (const entry of entries) {
    if (!entry.isDirectory()) continue;
    const fullPath = resolve(desktopInstallerReleasesRoot, entry.name);
    const details = await stat(fullPath).catch(() => null);
    folders.push({
      name: entry.name,
      path: fullPath,
      mtimeMs: details?.mtimeMs || 0,
    });
  }
  folders.sort((left, right) => right.mtimeMs - left.mtimeMs);
  for (const folder of folders.slice(keepCount)) {
    await rm(folder.path, { recursive: true, force: true });
  }
}

export async function runPublishExe(options = {}) {
  const appVersion = getRootAppVersion();
  const fingerprint = options.fingerprint || await computeDesktopBuildFingerprint();
  const baseUrl = buildBaseUrl();
  const exeFileName = getDesktopExeFileName(appVersion);
  const exeSourcePath = resolve(exeOutputRoot, exeFileName);
  const releaseDir = resolve(desktopInstallerReleasesRoot, appVersion);
  const latestDir = desktopInstallerLatestRoot;
  const versionedExeRelativePath = `/api/desktop/download/releases/${encodeURIComponent(appVersion)}/${encodeURIComponent(exeFileName)}`;
  const latestExeRelativePath = `/api/desktop/download/latest/${encodeURIComponent(exeFileName)}`;
  const manifestPayload = {
    schemaVersion: 1,
    channel: 'latest',
    appName: 'RMKCET Shine',
    version: appVersion,
    packageType: 'exe',
    preferredInstaller: 'exe',
    architecture: 'x64',
    publisher: String(process.env.SHINE_DESKTOP_PUBLISHER_DISPLAY_NAME || 'RMKCET Shine').trim(),
    publishedAt: new Date().toISOString(),
    releaseNotes: getReleaseNotesLines(),
    files: {
      exe: {
        fileName: exeFileName,
        relativePath: latestExeRelativePath,
        versionedRelativePath: versionedExeRelativePath,
      },
    },
  };

  try {
    await ensureExists(exeSourcePath, 'EXE installer artifact');
  } catch {
    await runMakeExe();
  }

  await ensureExists(exeSourcePath, 'EXE installer artifact');
  await ensureDir(desktopInstallerReleasesRoot);
  await cleanDir(releaseDir);
  await cleanDir(latestDir);
  await cp(exeSourcePath, resolve(releaseDir, exeFileName), { force: true });
  await cp(exeSourcePath, resolve(latestDir, exeFileName), { force: true });
  await writeFile(resolve(releaseDir, getReleaseManifestFileName()), JSON.stringify(manifestPayload, null, 2));
  await writeFile(resolve(latestDir, getReleaseManifestFileName()), JSON.stringify(manifestPayload, null, 2));
  await writeFile(resolve(releaseDir, 'build-fingerprint.json'), JSON.stringify(fingerprint, null, 2));
  await writeFile(desktopBuildFingerprintPath, JSON.stringify(fingerprint, null, 2));
  await rotateOldReleaseFolders(5);

  return {
    releaseDir,
    latestDir,
    downloadUrl: `${baseUrl}${latestExeRelativePath}`,
    manifestPayload,
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runPublishExe().then((result) => {
    console.log(`[desktop-release] Published EXE installer artifacts to ${dirname(resolve(result.latestDir, getReleaseManifestFileName()))}`);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

import { cp, writeFile } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';
import {
  appInstallerTemplatePath,
  cleanDir,
  desktopInstallerLatestRoot,
  desktopInstallerReleasesRoot,
  ensureDir,
  ensureExists,
  getDesktopAppInstallerFileName,
  getDesktopMsixFileName,
  getEnvFlag,
  getReleaseManifestFileName,
  getReleaseNotesLines,
  getRootAppVersion,
  msixOutputRoot,
  normalizeMsixVersion,
  writeTemplatedFile,
} from './release-utils.mjs';
import { runMakeMsix } from './make-msix.mjs';

function buildBaseUrl() {
  const raw = getEnvFlag('SHINE_DESKTOP_PUBLIC_BASE_URL', '');
  if (!/^https?:\/\//i.test(raw)) {
    throw new Error('SHINE_DESKTOP_PUBLIC_BASE_URL is required for publishing desktop installer artifacts.');
  }
  return raw.replace(/\/+$/, '');
}

export async function runPublishRelease() {
  const appVersion = getRootAppVersion();
  const msixVersion = normalizeMsixVersion(appVersion);
  const publisher = String(process.env.SHINE_DESKTOP_PACKAGE_PUBLISHER || 'CN=RMKCET SHINE').trim();
  const packageName = String(process.env.SHINE_DESKTOP_PACKAGE_NAME || 'RMKCET.Shine').trim();
  const architecture = 'x64';
  const baseUrl = buildBaseUrl();
  const msixFileName = getDesktopMsixFileName(appVersion);
  const appinstallerFileName = getDesktopAppInstallerFileName();
  const msixSourcePath = resolve(msixOutputRoot, msixFileName);
  const releaseDir = resolve(desktopInstallerReleasesRoot, appVersion);
  const latestDir = desktopInstallerLatestRoot;
  const versionedMsixRelativePath = `/downloads/desktop/releases/${encodeURIComponent(appVersion)}/${encodeURIComponent(msixFileName)}`;
  const latestAppInstallerRelativePath = `/downloads/desktop/latest/${encodeURIComponent(appinstallerFileName)}`;
  const manifestPayload = {
    schemaVersion: 1,
    channel: 'latest',
    appName: 'RMKCET Shine',
    version: appVersion,
    packageVersion: msixVersion,
    packageName,
    publisher,
    architecture,
    publishedAt: new Date().toISOString(),
    releaseNotes: getReleaseNotesLines(),
    files: {
      msix: {
        fileName: msixFileName,
        relativePath: versionedMsixRelativePath,
      },
      appinstaller: {
        fileName: appinstallerFileName,
        relativePath: latestAppInstallerRelativePath,
      },
    },
  };

  try {
    await ensureExists(msixSourcePath, 'MSIX artifact');
  } catch {
    await runMakeMsix();
  }

  await ensureExists(msixSourcePath, 'MSIX artifact');
  await ensureDir(desktopInstallerReleasesRoot);
  await cleanDir(releaseDir);
  await cleanDir(latestDir);
  await cp(msixSourcePath, resolve(releaseDir, msixFileName), { force: true });
  await writeTemplatedFile(appInstallerTemplatePath, resolve(latestDir, appinstallerFileName), {
    APPINSTALLER_URI: `${baseUrl}${latestAppInstallerRelativePath}`,
    PACKAGE_VERSION: msixVersion,
    PACKAGE_NAME: packageName,
    PUBLISHER: publisher,
    MSIX_URI: `${baseUrl}${versionedMsixRelativePath}`,
    ARCHITECTURE: architecture,
  });
  await writeFile(resolve(releaseDir, getReleaseManifestFileName()), JSON.stringify(manifestPayload, null, 2));
  await writeFile(resolve(latestDir, getReleaseManifestFileName()), JSON.stringify(manifestPayload, null, 2));

  return {
    releaseDir,
    latestDir,
    manifestPayload,
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runPublishRelease().then((result) => {
    console.log(`[desktop-release] Published desktop installer artifacts to ${dirname(resolve(result.latestDir, getReleaseManifestFileName()))}`);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

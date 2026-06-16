import { createHash } from 'node:crypto';
import { createReadStream } from 'node:fs';
import { cp, readdir, rm, stat, readFile, writeFile } from 'node:fs/promises';
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
  getDesktopReleaseVersion,
  getDesktopExeFileName,
  getEnvFlag,
  getReleaseManifestFileName,
  getReleaseNotesLines,
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

async function hashFileSha256(filePath) {
  return new Promise((resolvePromise, rejectPromise) => {
    const hash = createHash('sha256');
    const stream = createReadStream(filePath);
    stream.on('data', (chunk) => hash.update(chunk));
    stream.on('error', rejectPromise);
    stream.on('end', () => resolvePromise(hash.digest('hex')));
  });
}

function markLatestYmlAdminRequired(content) {
  const raw = String(content || '');
  if (/^\s+isAdminRightsRequired:\s*true\s*$/m.test(raw)) return raw;
  const lines = raw.split(/\r?\n/);
  const fileStartIndex = lines.findIndex((line, index) => (
    /^\s+-\s+url:\s*/.test(line) && lines.slice(0, index).some((candidate) => /^files:\s*$/.test(candidate))
  ));
  if (fileStartIndex < 0) return raw;

  let insertIndex = fileStartIndex + 1;
  for (let index = fileStartIndex + 1; index < lines.length; index += 1) {
    const line = lines[index];
    if (/^\S/.test(line) || /^\s+-\s+/.test(line)) break;
    insertIndex = index + 1;
    if (/^\s+size:\s*/.test(line)) break;
  }
  lines.splice(insertIndex, 0, '    isAdminRightsRequired: true');
  return lines.join('\n');
}

async function copyUpdaterArtifacts(sourceDir, releaseDir, latestDir) {
  const entries = await readdir(sourceDir, { withFileTypes: true }).catch(() => []);
  const updaterFiles = entries
    .filter((entry) => entry.isFile() && (/\.blockmap$/i.test(entry.name) || /^latest\.ya?ml$/i.test(entry.name)))
    .map((entry) => entry.name);
  for (const fileName of updaterFiles) {
    const sourcePath = resolve(sourceDir, fileName);
    if (/^latest\.ya?ml$/i.test(fileName)) {
      const latestYml = markLatestYmlAdminRequired(await readFile(sourcePath, 'utf8'));
      await writeFile(resolve(releaseDir, fileName), latestYml);
      await writeFile(resolve(latestDir, fileName), latestYml);
      continue;
    }
    await cp(sourcePath, resolve(releaseDir, fileName), { force: true });
    await cp(sourcePath, resolve(latestDir, fileName), { force: true });
  }
}

export async function runPublishExe(options = {}) {
  const appVersion = getDesktopReleaseVersion();
  const fingerprint = options.fingerprint || await computeDesktopBuildFingerprint();
  const baseUrl = buildBaseUrl();
  const exeFileName = getDesktopExeFileName();
  const exeSourcePath = resolve(exeOutputRoot, exeFileName);
  const releaseDir = resolve(desktopInstallerReleasesRoot, appVersion);
  const latestDir = desktopInstallerLatestRoot;
  const versionedExeRelativePath = `/api/desktop/download/releases/${encodeURIComponent(appVersion)}/${encodeURIComponent(exeFileName)}`;
  const latestExeRelativePath = `/api/desktop/download/latest/${encodeURIComponent(exeFileName)}`;
  try {
    await ensureExists(exeSourcePath, 'EXE installer artifact');
  } catch {
    await runMakeExe();
  }

  await ensureExists(exeSourcePath, 'EXE installer artifact');
  const exeDetails = await stat(exeSourcePath);
  const exeSha256 = await hashFileSha256(exeSourcePath);
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
        size: exeDetails.size,
        sha256: exeSha256,
      },
    },
  };
  await ensureDir(desktopInstallerReleasesRoot);
  await cleanDir(releaseDir);
  await cleanDir(latestDir);
  await cp(exeSourcePath, resolve(releaseDir, exeFileName), { force: true });
  await cp(exeSourcePath, resolve(latestDir, exeFileName), { force: true });
  await copyUpdaterArtifacts(exeOutputRoot, releaseDir, latestDir);
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

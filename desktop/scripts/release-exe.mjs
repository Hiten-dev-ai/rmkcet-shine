import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { readFile, stat } from 'node:fs/promises';
import { runMakeExe } from './make-exe.mjs';
import { runPublishExe } from './publish-exe.mjs';
import {
  computeDesktopBuildFingerprint,
  desktopBuildFingerprintPath,
  desktopInstallerLatestRoot,
  getDesktopReleaseVersion,
  getDesktopExeFileName,
  getNextDesktopReleaseVersion,
  getReleaseManifestFileName,
  hasPublishedDesktopExe,
  writeRuntimeReleaseConfig,
} from './release-utils.mjs';

async function getLatestReleaseStatus(fingerprint) {
  const version = getDesktopReleaseVersion();
  const exePath = resolve(desktopInstallerLatestRoot, getDesktopExeFileName());
  const manifestPath = resolve(desktopInstallerLatestRoot, getReleaseManifestFileName());
  try {
    const [storedFingerprint, manifest] = await Promise.all([
      readFile(desktopBuildFingerprintPath, 'utf8').then((raw) => JSON.parse(raw)),
      readFile(manifestPath, 'utf8').then((raw) => JSON.parse(raw)),
      stat(exePath),
    ]);
    const fingerprintMatches = storedFingerprint?.hash === fingerprint.hash
      && storedFingerprint?.version === version
      && manifest?.version === version
      && !!manifest?.files?.exe?.relativePath;
    if (!fingerprintMatches) return 'stale';
    return String(manifest.files.exe.relativePath || '').startsWith('/api/desktop/download/') ? 'current' : 'republish';
  } catch {
    return 'stale';
  }
}

export async function runReleaseExe() {
  const hadPublishedExe = hasPublishedDesktopExe();
  process.env.SHINE_DESKTOP_RELEASE_VERSION ||= getNextDesktopReleaseVersion();
  await writeRuntimeReleaseConfig();
  const fingerprint = await computeDesktopBuildFingerprint();
  const releaseMode = hadPublishedExe ? 'update' : 'bootstrap';
  console.log(
    hadPublishedExe
      ? `[desktop-release] Existing standalone EXE found; publishing update package ${fingerprint.version}.`
      : `[desktop-release] No standalone EXE found; creating initial standalone EXE ${fingerprint.version}.`,
  );
  if (process.env.SHINE_DESKTOP_SKIP_UNCHANGED === '1') {
    const status = await getLatestReleaseStatus(fingerprint);
    if (status === 'current') {
      console.log(`[desktop-release] EXE release ${fingerprint.version} is unchanged; reusing data/desktop-installer/latest.`);
      return {
        skipped: true,
        exe: { appVersion: fingerprint.version },
        published: { latestDir: desktopInstallerLatestRoot },
      };
    }
    if (status === 'republish') {
      console.log(`[desktop-release] EXE release ${fingerprint.version} is unchanged; refreshing release manifest only.`);
      const published = await runPublishExe({ fingerprint });
      return {
        skipped: true,
        republished: true,
        exe: { appVersion: fingerprint.version },
        published,
      };
    }
  }
  const exe = await runMakeExe();
  const published = await runPublishExe({ fingerprint });
  return {
    releaseMode,
    exe,
    published,
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runReleaseExe().then((result) => {
    console.log(`[desktop-release] EXE release ${result.exe.appVersion} is ${result.skipped ? 'already current' : 'ready'}.`);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

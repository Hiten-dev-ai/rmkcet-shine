import { build, Platform } from 'electron-builder';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import {
  buildClientDesktopShell,
  cleanDir,
  clientDesktopDistRoot,
  desktopRoot,
  ensureExists,
  exeOutputRoot,
  generatedRuntimeConfigPath,
  getDesktopReleaseVersion,
  getDesktopExeFileName,
  readDesktopPackageJson,
  writeRuntimeReleaseConfig,
} from './release-utils.mjs';

const DEFAULT_APP_ID = 'RMKCET.Shine.App';

function buildUpdaterFeedUrl() {
  const explicit = String(process.env.SHINE_DESKTOP_UPDATER_FEED_URL || process.env.SHINE_DESKTOP_RELEASE_CHANNEL_URL || '').trim();
  if (/^https?:\/\//i.test(explicit)) return explicit.replace(/\/+$/, '');
  const publicBaseUrl = String(process.env.SHINE_DESKTOP_PUBLIC_BASE_URL || '').trim();
  if (/^https?:\/\//i.test(publicBaseUrl)) {
    return `${publicBaseUrl.replace(/\/+$/, '')}/api/desktop/updater`;
  }
  return 'http://127.0.0.1:5001/api/desktop/updater';
}

export async function runMakeExe() {
  const desktopPackage = await readDesktopPackageJson();
  const appVersion = getDesktopReleaseVersion();
  const productName = String(desktopPackage.productName || 'RMKCET Shine').trim();
  const description = String(process.env.SHINE_DESKTOP_PACKAGE_DESCRIPTION || 'RMKCET Shine Windows desktop client.').trim();
  const exeFileName = getDesktopExeFileName();
  const certPath = String(process.env.SHINE_DESKTOP_CERT_PATH || '').trim();
  const certPassword = String(process.env.SHINE_DESKTOP_CERT_PASSWORD || '').trim();
  const publisherName = String(process.env.SHINE_DESKTOP_PUBLISHER_DISPLAY_NAME || productName).trim();
  const hasWindowsSigningCert = certPath.length > 0;

  await buildClientDesktopShell();
  await writeRuntimeReleaseConfig();
  await cleanDir(exeOutputRoot);
  await ensureExists(clientDesktopDistRoot, 'Desktop renderer build');

  await build({
    targets: Platform.WINDOWS.createTarget(['nsis']),
    config: {
      appId: String(process.env.SHINE_DESKTOP_APP_ID || DEFAULT_APP_ID).trim(),
      productName,
      artifactName: exeFileName,
      directories: {
        output: exeOutputRoot,
      },
      win: {
        icon: resolve(desktopRoot, 'assets', 'icon.ico'),
        executableName: productName,
        publisherName,
        signAndEditExecutable: hasWindowsSigningCert,
        signingHashAlgorithms: ['sha256'],
        ...(hasWindowsSigningCert ? {
          certificateFile: certPath,
          certificatePassword: certPassword || undefined,
        } : {}),
      },
      files: [
        '**/*',
        '!out{,/**}',
        '!.workspace{,/**}',
        '!runtime{,/**}',
        '!tmp-electron-test{,/**}',
        '!tmp-asar-extract{,/**}',
        '!scripts{,/**}',
        '!Package.appxmanifest',
        '!appinstaller.template.xml',
      ],
      extraMetadata: {
        version: appVersion,
        productName,
        description,
      },
      asar: true,
      npmRebuild: false,
      buildDependenciesFromSource: false,
      compression: 'normal',
      extraResources: [
        {
          from: resolve(desktopRoot, 'assets'),
          to: 'assets',
        },
        {
          from: generatedRuntimeConfigPath,
          to: 'release-config.json',
        },
        {
          from: clientDesktopDistRoot,
          to: 'dist-desktop',
        },
      ],
      nsis: {
        include: resolve(desktopRoot, 'installer.nsh'),
        oneClick: false,
        perMachine: true,
        allowElevation: true,
        allowToChangeInstallationDirectory: false,
        deleteAppDataOnUninstall: false,
        createDesktopShortcut: 'always',
        createStartMenuShortcut: true,
        shortcutName: productName,
        uninstallDisplayName: productName,
      },
      publish: [
        {
          provider: 'generic',
          url: buildUpdaterFeedUrl(),
        },
      ],
    },
    projectDir: desktopRoot,
  });

  return {
    appVersion,
    exeFileName,
    exeTargetPath: resolve(exeOutputRoot, exeFileName),
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runMakeExe().then((result) => {
    console.log(`[desktop-release] EXE installer created at ${result.exeTargetPath}`);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

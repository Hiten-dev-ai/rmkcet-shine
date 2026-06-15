import { build, Platform } from 'electron-builder';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import {
  buildClientDesktopShellIfMissing,
  cleanDir,
  clientDesktopDistRoot,
  desktopRoot,
  ensureExists,
  exeOutputRoot,
  generatedRuntimeConfigPath,
  getDesktopExeFileName,
  getRootAppVersion,
  readDesktopPackageJson,
  writeRuntimeReleaseConfig,
} from './release-utils.mjs';

const DEFAULT_APP_ID = 'dev.rmkcet.shine';

export async function runMakeExe() {
  const desktopPackage = await readDesktopPackageJson();
  const appVersion = getRootAppVersion();
  const productName = String(desktopPackage.productName || 'RMKCET Shine').trim();
  const description = String(process.env.SHINE_DESKTOP_PACKAGE_DESCRIPTION || 'RMKCET Shine Windows desktop client.').trim();
  const exeFileName = getDesktopExeFileName(appVersion);

  await buildClientDesktopShellIfMissing();
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
          from: generatedRuntimeConfigPath,
          to: 'release-config.json',
        },
        {
          from: clientDesktopDistRoot,
          to: 'dist-desktop',
        },
      ],
      nsis: {
        oneClick: false,
        perMachine: false,
        allowElevation: true,
        allowToChangeInstallationDirectory: true,
        deleteAppDataOnUninstall: false,
        createDesktopShortcut: 'always',
        createStartMenuShortcut: true,
        shortcutName: productName,
        uninstallDisplayName: productName,
      },
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

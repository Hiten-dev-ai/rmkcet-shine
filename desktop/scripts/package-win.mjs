import { packager } from '@electron/packager';
import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import {
  buildClientDesktopShellIfMissing,
  cleanDir,
  copyMsixAssets,
  desktopRoot,
  generatedRuntimeConfigPath,
  getRootAppVersion,
  manifestTemplatePath,
  normalizeMsixVersion,
  packagedOutputRoot,
  readDesktopPackageJson,
  writeRuntimeReleaseConfig,
  writeTemplatedFile,
} from './release-utils.mjs';

const DEFAULT_PACKAGE_NAME = 'RMKCET.Shine';
const DEFAULT_PUBLISHER = 'CN=RMKCET SHINE';

export async function runPackageWin() {
  const desktopPackage = await readDesktopPackageJson();
  const appVersion = getRootAppVersion();
  const displayName = String(desktopPackage.productName || 'RMKCET Shine').trim();
  const publisher = String(process.env.SHINE_DESKTOP_PACKAGE_PUBLISHER || DEFAULT_PUBLISHER).trim();
  const packageName = String(process.env.SHINE_DESKTOP_PACKAGE_NAME || DEFAULT_PACKAGE_NAME).trim();
  const publisherDisplayName = String(process.env.SHINE_DESKTOP_PUBLISHER_DISPLAY_NAME || 'RMKCET Shine').trim();
  const description = String(process.env.SHINE_DESKTOP_PACKAGE_DESCRIPTION || 'RMKCET Shine Windows desktop client.').trim();

  await buildClientDesktopShellIfMissing();
  await writeRuntimeReleaseConfig();
  await cleanDir(packagedOutputRoot);

  const packagePaths = await packager({
    dir: desktopRoot,
    out: packagedOutputRoot,
    overwrite: true,
    asar: true,
    platform: 'win32',
    arch: 'x64',
    prune: true,
    icon: resolve(desktopRoot, 'assets', 'icon.ico'),
    executableName: displayName,
    appVersion,
    name: displayName,
    win32metadata: {
      ProductName: displayName,
      CompanyName: publisherDisplayName,
      FileDescription: description,
      OriginalFilename: `${displayName}.exe`,
    },
    extraResource: [
      generatedRuntimeConfigPath,
      resolve(desktopRoot, '..', 'client', 'dist-desktop'),
    ],
    ignore: [
      /^\/\.workspace($|\/)/,
      /^\/out($|\/)/,
      /^\/runtime($|\/)/,
      /^\/tmp-electron-test($|\/)/,
      /^\/scripts($|\/)/,
      /^\/Package\.appxmanifest$/,
      /^\/appinstaller\.template\.xml$/,
    ],
  });

  const packageDir = packagePaths[0];
  if (!packageDir) {
    throw new Error('Electron packaging did not produce a Windows app directory.');
  }

  const manifestPath = resolve(packageDir, 'Package.appxmanifest');
  const assetsDir = resolve(packageDir, 'Assets');
  await copyMsixAssets(assetsDir);
  await writeTemplatedFile(manifestTemplatePath, manifestPath, {
    PACKAGE_NAME: packageName,
    PUBLISHER: publisher,
    PACKAGE_VERSION: normalizeMsixVersion(appVersion),
    DISPLAY_NAME: displayName,
    PUBLISHER_DISPLAY_NAME: publisherDisplayName,
    DESCRIPTION: description,
  });

  return {
    packageDir,
    manifestPath,
    displayName,
    packageName,
    publisher,
    publisherDisplayName,
    description,
    appVersion,
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runPackageWin().then((result) => {
    console.log(`[desktop-release] Packaged Windows app at ${result.packageDir}`);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

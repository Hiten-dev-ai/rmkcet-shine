import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import {
  cleanDir,
  ensureDir,
  ensureWinappInstalled,
  getDesktopMsixFileName,
  getEnvFlag,
  getRootAppVersion,
  msixOutputRoot,
  normalizeMsixVersion,
  runCommand,
} from './release-utils.mjs';
import { runPackageWin } from './package-win.mjs';

export async function runMakeMsix() {
  const winapp = ensureWinappInstalled();
  const packageResult = await runPackageWin();
  const appVersion = getRootAppVersion();
  const msixVersion = normalizeMsixVersion(appVersion);
  const msixFileName = getDesktopMsixFileName(appVersion);
  const msixTargetPath = resolve(msixOutputRoot, msixFileName);
  const certPath = getEnvFlag('SHINE_DESKTOP_CERT_PATH', '');
  const certPassword = getEnvFlag('SHINE_DESKTOP_CERT_PASSWORD', '');
  const installDevCert = getEnvFlag('SHINE_DESKTOP_INSTALL_DEV_CERT', 'false').toLowerCase() === 'true';
  const signMode = certPath ? 'pfx' : 'dev';

  await ensureDir(msixOutputRoot);
  await cleanDir(msixOutputRoot);

  const args = [
    'pack',
    packageResult.packageDir,
    '--manifest',
    packageResult.manifestPath,
    '--output',
    msixTargetPath,
    '--executable',
    `${packageResult.displayName}.exe`,
  ];

  if (signMode === 'pfx') {
    args.push('--cert', certPath);
    if (certPassword) args.push('--cert-password', certPassword);
  } else {
    args.push('--generate-cert');
    if (installDevCert) args.push('--install-cert');
  }

  await runCommand(winapp.command, [...winapp.prefixArgs, ...args], {
    title: `Creating signed MSIX ${msixFileName} (${msixVersion})`,
  });

  return {
    ...packageResult,
    appVersion,
    msixVersion,
    msixFileName,
    msixTargetPath,
    signMode,
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runMakeMsix().then((result) => {
    console.log(`[desktop-release] MSIX created at ${result.msixTargetPath}`);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

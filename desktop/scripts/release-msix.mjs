import { fileURLToPath } from 'node:url';
import { resolve } from 'node:path';
import { runMakeMsix } from './make-msix.mjs';
import { runPublishRelease } from './publish-release.mjs';

export async function runReleaseMsix() {
  const msix = await runMakeMsix();
  const published = await runPublishRelease();
  return {
    msix,
    published,
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  runReleaseMsix().then((result) => {
    console.log(`[desktop-release] Release ${result.msix.appVersion} is ready.`);
  }).catch((error) => {
    console.error(error instanceof Error ? error.message : String(error));
    process.exit(1);
  });
}

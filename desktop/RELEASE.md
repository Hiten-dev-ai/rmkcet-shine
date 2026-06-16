# RMKCET Shine Windows Release

This repo now produces Windows desktop release artifacts based on:

- packaged Electron app folder
- signed `.msix`
- stable `.appinstaller` update URL
- direct-download `.exe` installer for internal website rollout
- `electron-updater` metadata for NSIS desktop updates

## Required environment

Set these before packaging a hosted desktop release:

```powershell
$env:SHINE_DESKTOP_RELEASE_API_ORIGIN = "https://rmkcetshine.me"
$env:SHINE_DESKTOP_PUBLIC_BASE_URL = "https://rmkcetshine.me"
$env:SHINE_DESKTOP_PACKAGE_PUBLISHER = "CN=Your Trusted Publisher"
$env:SHINE_DESKTOP_PUBLISHER_DISPLAY_NAME = "RMKCET Shine"
```

Optional:

```powershell
$env:SHINE_DESKTOP_PACKAGE_NAME = "RMKCET.Shine"
$env:SHINE_DESKTOP_PACKAGE_DESCRIPTION = "RMKCET Shine Windows desktop client."
$env:SHINE_DESKTOP_RELEASE_NOTES = "Line 1`nLine 2"
$env:SHINE_DESKTOP_UPDATER_FEED_URL = "https://rmkcetshine.me/api/desktop/updater"
$env:SHINE_DESKTOP_CERT_PATH = "C:\\path\\to\\signing-cert.pfx"
$env:SHINE_DESKTOP_CERT_PASSWORD = "secret"
$env:SHINE_DESKTOP_INSTALL_DEV_CERT = "true"
```

If `SHINE_DESKTOP_CERT_PATH` is omitted, the MSIX step falls back to local development signing. Use `SHINE_DESKTOP_INSTALL_DEV_CERT=true` only when you explicitly want the generated test cert installed on the current machine. Use a stable trusted publisher identity for real user releases.

## Local self-signed EXE signing

For internal testing, generate a local self-signed code-signing certificate:

```bash
desktop/scripts/create-self-signed-cert.sh
source desktop/.release-local.env
```

On Windows, use PowerShell:

```powershell
powershell -ExecutionPolicy Bypass -File desktop/scripts/create-self-signed-cert.ps1
desktop\.release-local.cmd
```

Then run the EXE release:

```bash
npm run desktop:release:exe
```

Generated local files are ignored by git:

- `desktop/certs/shine-selfsigned-codesign.pfx`
- `desktop/certs/shine-selfsigned-codesign.crt`
- `desktop/.release-local.env`
- `desktop/.release-local.cmd`

Self-signed signing does not remove Windows SmartScreen warnings for normal users. To make a Windows test PC trust this build, import `desktop/certs/shine-selfsigned-codesign.crt` into both:

- Trusted Root Certification Authorities
- Trusted Publishers

## Update pickup timing

Packaged desktop apps check for updates:

- during startup before opening the main app
- once again shortly after launch
- periodically while running, using the notification poll interval with a 10 minute minimum
- when the user clicks **Check Updates** in the tray/app settings

Existing installed versions that still use the older custom updater can still move to the new updater build because the EXE release command continues to publish `release.json` and `/api/desktop/installer/exe`.

## Release commands

From the repo root:

```powershell
npm run desktop:package
npm run desktop:exe
npm run desktop:msix
npm run desktop:publish
npm run desktop:publish:exe
```

Or run the full pipeline:

```powershell
npm run desktop:release
npm run desktop:release:exe
```

## Output locations

- packaged app folder: `desktop/out/packaged`
- built EXE installer: `desktop/out/exe`
- built MSIX: `desktop/out/msix`
- published installer channel: `data/desktop-installer`

Published files are exposed by the server through:

- `/api/desktop/installer`
- `/api/desktop/installer/meta`
- `/api/desktop/updater/latest.yml`
- `/api/desktop/updater/<installer-or-blockmap-file>`
- `/downloads/desktop/latest/...`
- `/downloads/desktop/releases/<version>/...`

## Release checklist

1. Bump the root app version in `package.json`.
2. Build and smoke-test web + desktop client locally.
3. Set release env vars for hosted API origin and trusted publisher identity.
4. Run `npm run desktop:release` for the MSIX channel or `npm run desktop:release:exe` for the website `.exe` and updater channel.
5. Start the server and verify `/api/desktop/installer`.
6. Test the chosen installer flow on a clean Windows machine.
7. Confirm the installed app opens the hosted Shine server, not localhost.
8. Publish release notes and share the installer page URL with users.

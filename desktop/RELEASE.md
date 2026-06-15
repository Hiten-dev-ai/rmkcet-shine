# RMKCET Shine Windows Release

This repo now produces Windows desktop release artifacts based on:

- packaged Electron app folder
- signed `.msix`
- stable `.appinstaller` update URL
- direct-download `.exe` installer for internal website rollout

## Required environment

Set these before packaging a hosted desktop release:

```powershell
$env:SHINE_DESKTOP_RELEASE_API_ORIGIN = "https://shine.athergrid.dev"
$env:SHINE_DESKTOP_PUBLIC_BASE_URL = "https://shine.athergrid.dev"
$env:SHINE_DESKTOP_PACKAGE_PUBLISHER = "CN=Your Trusted Publisher"
$env:SHINE_DESKTOP_PUBLISHER_DISPLAY_NAME = "RMKCET Shine"
```

Optional:

```powershell
$env:SHINE_DESKTOP_PACKAGE_NAME = "RMKCET.Shine"
$env:SHINE_DESKTOP_PACKAGE_DESCRIPTION = "RMKCET Shine Windows desktop client."
$env:SHINE_DESKTOP_RELEASE_NOTES = "Line 1`nLine 2"
$env:SHINE_DESKTOP_CERT_PATH = "C:\\path\\to\\signing-cert.pfx"
$env:SHINE_DESKTOP_CERT_PASSWORD = "secret"
$env:SHINE_DESKTOP_INSTALL_DEV_CERT = "true"
```

If `SHINE_DESKTOP_CERT_PATH` is omitted, the MSIX step falls back to local development signing. Use `SHINE_DESKTOP_INSTALL_DEV_CERT=true` only when you explicitly want the generated test cert installed on the current machine. Use a stable trusted publisher identity for real user releases.

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
- `/downloads/desktop/latest/...`
- `/downloads/desktop/releases/<version>/...`

## Release checklist

1. Bump the root app version in `package.json`.
2. Build and smoke-test web + desktop client locally.
3. Set release env vars for hosted API origin and trusted publisher identity.
4. Run `npm run desktop:release` for the MSIX channel or `npm run desktop:release:exe` for the website `.exe` channel.
5. Start the server and verify `/api/desktop/installer`.
6. Test the chosen installer flow on a clean Windows machine.
7. Confirm the installed app opens the hosted Shine server, not localhost.
8. Publish release notes and share the installer page URL with users.

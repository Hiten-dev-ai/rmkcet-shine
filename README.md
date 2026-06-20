# RMKCET Shine

RMKCET Shine is a standalone rebuild of the college result, notice, CDP, counselor activity, and desktop WhatsApp workflow system.

The rebuild uses:

- React + Vite + TypeScript for the client
- Node.js + Hono + TypeScript for the API server
- SQLite through `better-sqlite3` for local operational data
- Electron for the Windows desktop shell and WhatsApp send workspace

This repository is independent from the legacy Flask project.

## Repository Layout

```text
client/      React frontend, Vite config, feature tabs, UI styles
server/      Hono API, SQLite schema/read models, auth, backups, CDP parsing
desktop/     Electron shell, desktop bridge, tray/window/WhatsApp workspace
data/        Runtime SQLite DB, backups, archives, notice assets, installer output
deploy/      Deployment support files
logs/        Runtime logs
scripts/     Shared helper scripts used by launchers
start.bat    Windows launcher menu
start.sh     Linux/VPS launcher menu
install.sh   Linux service installer helper
```

Do not commit secrets, local databases, generated packages, or runtime logs.

## Requirements

- Node.js 22+ recommended
- npm
- Windows for Electron desktop testing
- Chrome or Edge for desktop WhatsApp Web mode
- WhatsApp Desktop from Microsoft Store for app mode
- SQLite database stored under `data/`

## First Setup

Install dependencies for every workspace:

```powershell
npm.cmd install
npm.cmd run install-all
```

Create a local `.env` in the repo root. Keep it out of git.

```env
HOST=localhost
PORT=5001
CLIENT_ORIGIN=http://localhost:5000
SERVER_ORIGIN=http://localhost:5001
DESKTOP_SHELL_ORIGIN=http://localhost:5123
SHINE_DB_PATH=D:\RMKCET\rmkcet-shine\data\rmkcet.db
COUNTRY_CODE=91

DEFAULT_SYSTEM_ADMIN_EMAIL=admin@rmkcet.ac.in
DEFAULT_SYSTEM_ADMIN_PASSWORD=change-this-password

SMTP_SERVER=smtp.gmail.com
SMTP_PORT=587
SMTP_USERNAME=
SMTP_PASSWORD=
EMAIL_FROM=
```

The server also stores many app settings in SQLite through the Admin Settings UI, including Google OAuth, SMTP, desktop send workspace, notifications, backup mode, and CDP formatting.

## Running Locally

### Windows Launcher

Use:

```powershell
.\start.bat
```

Menu options:

```text
1. Web app only
2. Desktop dev-shell
3. Desktop app mode (desktop only)
4. Server only
5. Build/publish desktop update package
6. Production web + desktop app
```

Important ports:

```text
Web client        http://localhost:5000
API server        http://localhost:5001
Desktop shell     http://localhost:5123
```

Option 6 waits for the production preview and server to become reachable before opening the browser.

### Manual npm Scripts

```powershell
npm.cmd run dev                 # server + web client
npm.cmd run dev:server          # server only
npm.cmd run dev:client          # client only
npm.cmd run desktop:app         # server + built desktop shell + Electron
npm.cmd run prod:web            # production server + web preview
npm.cmd run prod:desktop-web    # production server + web preview + Electron
npm.cmd run build               # server + client build
```

### Linux/VPS Launcher

Use:

```bash
./start.sh
```

Typical VPS production mode binds the web preview to port `5000` and API to port `5001`.

For a public domain such as `https://shine.athergrid.dev`, ensure:

- Nginx points `/` to the web client on `5000`
- Nginx points `/api` and `/auth` to the API server on `5001`
- `CLIENT_ORIGIN` is the public HTTPS origin
- `SERVER_ORIGIN` is the public HTTPS origin when OAuth redirects need to use the domain
- `CLIENT_ORIGINS` includes local preview origins if needed

## Google OAuth

Google OAuth redirect URI:

```text
https://your-domain.example/auth/google/callback
```

For the current hosted domain:

```text
https://shine.athergrid.dev/auth/google/callback
```

The desktop client signs in through a browser-style OAuth flow and returns to the Electron shell. For local desktop testing, the server still runs on `localhost:5001`; do not point desktop option 3 at the public domain unless you are intentionally testing hosted auth.

If Google shows a redirect URI policy error, add the exact redirect URI in Google Cloud Console for the OAuth client.

## Desktop App Notes

The Electron shell provides:

- Tray lifecycle
- Desktop settings
- Native Windows notifications
- Floating/embedded WhatsApp send workspace
- Browser-based desktop OAuth handoff
- Server connectivity/recovery page

Desktop send modes:

- App mode opens `whatsapp://send` links directly.
- Web mode opens WhatsApp Web through a managed Chrome/Edge profile.
- Embedded workspace uses an Electron BrowserView when available.

When testing desktop changes, restart option 3 or option 6 after editing `desktop/src/main.mjs` because Electron main-process code is loaded at startup.

## Desktop Locator CSV

Packaged desktop builds can use a public CSV locator only when the primary API cannot be reached.

CSV format:

```csv
key,value
apiOrigin,https://shine.athergrid.dev
releaseChannelBaseUrl,https://shine.athergrid.dev/api/desktop/installer
downloadPageUrl,https://shine.athergrid.dev/api/desktop/installer
updatedAt,2026-06-20
message,Primary Shine server endpoint
```

Publish the sheet as CSV and provide its public CSV URL through:

```env
SHINE_DESKTOP_LOCATOR_CSV_URL=https://docs.google.com/spreadsheets/d/.../pub?output=csv
```

Users should not manually enter arbitrary server URLs in the app.

## Data And Backups

Runtime data lives in:

```text
data/rmkcet.db
data/backups/
data/archives/
data/notice_assets/
data/desktop-installer/
```

Important rules:

- Back up `data/rmkcet.db` before destructive database operations.
- Do not commit `data/`.
- Do not delete `data/`, `.env`, `desktop/runtime/`, or release artifacts unless you intentionally rotate generated files.
- SQLite timestamps are stored in UTC. UI code should use UTC-aware formatters before displaying them.

## Core Features

- Role-based login: admin, principal/higher official, HoD, DEO, counselor
- Multi-role accounts through a shared `login_email`
- Role switcher for linked accounts
- Dashboard completion summaries
- Reports/test database upload and mark editing
- Counselor result sending through WhatsApp
- Notices and notice sending
- Message logs with date/month/year filters
- Session monitoring with idle status and date filtering
- CDP subject management, attendance completion, proposed lecture plan, mark entry
- Notification center, desktop notifications, and foreground toasts
- Admin settings for server, desktop, notification, OAuth, SMTP, backup, tutorial, and formatting behavior
- In-app role-aware tutorial guide

## Checks Before Pushing

Run the checks relevant to the files touched:

```powershell
npm.cmd run build --prefix server
npx.cmd tsc -b
npm.cmd run build --prefix client
npm.cmd run build:desktop-shell --prefix client
node --check desktop\src\main.mjs
```

For a full web production smoke:

```powershell
npm.cmd run prod:web
```

For desktop app mode:

```powershell
npm.cmd run desktop:app
```

## Troubleshooting

### White screen in option 6

Option 6 should wait for the client/server before opening the browser. If a white screen still appears:

1. Hard refresh the browser.
2. Stop option 6.
3. Kill processes on ports `5000`, `5001`, and `5123`.
4. Run option 6 again.

### OAuth 502 or redirect issues

- Check Nginx upstreams for `/auth` and `/api`.
- Check `SERVER_ORIGIN`, `CLIENT_ORIGIN`, and Google redirect URI.
- Check that the API server is actually running on `5001`.

### WhatsApp Web first send reloads

The desktop web-mode handoff uses a managed Chrome/Edge debug profile. Restart the Electron app after changes to `desktop/src/main.mjs`.

### Notifications do not appear while minimized

- Confirm Desktop Notifications are enabled.
- Confirm `desktop_notification_poll_seconds` is set, default `30`.
- Native notifications only show from the desktop client, not the web browser.

### Uploaded times look wrong

SQLite stores timestamps in UTC. UI display should use `formatUtcSqlDateTime` or an equivalent UTC-aware formatter.

## Git Hygiene

Before committing:

```powershell
git status --short
git diff --stat
```

Avoid committing:

- `.env`
- `data/`
- `logs/`
- `client/dist/`
- `client/dist-desktop/`
- `desktop/out/`
- generated installers
- local browser profiles or Electron temp folders

## Current Public Domain

Current hosted domain:

```text
https://shine.athergrid.dev
```

Use this as the public app origin, OAuth redirect base, and desktop release/download host unless the deployment domain changes.

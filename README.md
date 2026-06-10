# RMKCET Shine

Standalone rewrite of RMKCET Shine built on React + Vite + TypeScript for the client and Node + Hono + TypeScript for the server.

This repo is the new home for the rebuild and is meant to stay independent from the legacy Flask project.

## Goals

- Keep Shine as the product
- Match the current Shine UI and workflow first
- Keep the local SQLite data model as the base
- Avoid mixing CDP-specific features into the phase-1 rebuild

## Layout

- `client/` - React + Vite frontend
- `server/` - Hono API and backend logic
- `data/` - local SQLite DB, backups, archives, and notice assets

## Run

```powershell
npm.cmd install
npm.cmd run install-all
npm.cmd run dev
```

Client: `http://[::1]:5000`

Server: `http://[::1]:5001`

## Environment

Copy the local `.env` and keep secrets out of git.

```text
CLIENT_ORIGIN=http://[::1]:5000
SERVER_ORIGIN=http://[::1]:5001
SHINE_DB_PATH=D:\RMKCET\rmkcet-shine\data\rmkcet.db
PORT=5001
HOST=::1
```

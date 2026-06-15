#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

need_command() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "[ERROR] $1 is not installed or not in PATH." >&2
    exit 1
  fi
}

ensure_deps() {
  local dir="$1"
  local label="$2"
  if [ ! -d "$dir/node_modules" ]; then
    echo "[INFO] Installing $label dependencies..."
    npm install --prefix "$dir"
  fi
}

need_command node
need_command npm

if [ ! -d node_modules ]; then
  echo "[INFO] Installing root dependencies..."
  npm install
fi
ensure_deps client "client"
ensure_deps server "server"
ensure_deps desktop "desktop"

echo
echo "============================================"
echo " RMKCET Shine Rebuild"
echo " Linux / Server Launcher"
echo "============================================"
echo
echo "Choose launch mode:"
echo "  [1] Web app only"
echo "  [2] Desktop dev-shell"
echo "  [3] Desktop app mode (desktop only)"
echo "  [4] Server only"
echo "  [5] Build/publish desktop update package"
echo "  [6] Production web + desktop app"
read -r -p "Enter your choice: " launch_mode

kill_port() {
  local port="$1"
  local pids
  pids="$(lsof -ti :"$port" 2>/dev/null || true)"
  if [ -n "$pids" ]; then
    echo "[INFO] Killing process on port $port: $pids"
    kill -9 $pids 2>/dev/null || true
  fi
}

if [ "$launch_mode" = "5" ]; then
  echo
  echo "Choose package type:"
  echo "  [1] Local EXE installer build"
  echo "  [2] Hosted EXE website/update package"
  read -r -p "Enter your choice: " package_mode
  default_origin="${SHINE_DESKTOP_RELEASE_API_ORIGIN:-https://shine.athergrid.dev}"
  read -r -p "Enter Shine URL for packaged app [$default_origin]: " package_origin
  package_origin="${package_origin:-$default_origin}"
  export SHINE_DESKTOP_RELEASE_API_ORIGIN="$package_origin"
  export SHINE_DESKTOP_PUBLIC_BASE_URL="$package_origin"
  read -r -p "Enter public locator CSV URL (optional) [${SHINE_DESKTOP_LOCATOR_CSV_URL:-}]: " locator_csv
  if [ -n "$locator_csv" ]; then export SHINE_DESKTOP_LOCATOR_CSV_URL="$locator_csv"; fi
  read -r -p "Enter release channel URL (optional) [${SHINE_DESKTOP_RELEASE_CHANNEL_URL:-}]: " release_channel
  if [ -n "$release_channel" ]; then export SHINE_DESKTOP_RELEASE_CHANNEL_URL="$release_channel"; fi

  if [ "$package_mode" = "1" ]; then
    npm run desktop:exe
  else
    npm run desktop:release:exe
  fi
  echo "[SUCCESS] Desktop EXE artifacts are ready."
  echo "Latest manifest: data/desktop-installer/latest/release.json"
  exit 0
fi

case "$launch_mode" in
  1)
    kill_port 5000
    kill_port 5001
    npm run dev:web
    ;;
  2)
    kill_port 5000
    kill_port 5001
    npm run dev:desktop
    ;;
  3)
    kill_port 5001
    kill_port 5123
    npm run desktop:app
    ;;
  4)
    kill_port 5001
    npm run dev:server
    ;;
  6)
    kill_port 5000
    kill_port 5001
    kill_port 5123
    default_origin="${SHINE_DESKTOP_RELEASE_API_ORIGIN:-https://shine.athergrid.dev}"
    read -r -p "Enter hosted Shine server domain [$default_origin]: " package_origin
    package_origin="${package_origin:-$default_origin}"
    export SHINE_DESKTOP_RELEASE_API_ORIGIN="$package_origin"
    export SHINE_DESKTOP_PUBLIC_BASE_URL="$package_origin"
    export SHINE_DESKTOP_RELEASE_CHANNEL_URL="$package_origin/api/desktop/installer"
    read -r -p "Enter public Google Sheet locator CSV URL (optional) [${SHINE_DESKTOP_LOCATOR_CSV_URL:-}]: " locator_csv
    if [ -n "$locator_csv" ]; then export SHINE_DESKTOP_LOCATOR_CSV_URL="$locator_csv"; fi
    export SHINE_DESKTOP_SKIP_UNCHANGED=1
    echo "[INFO] Hosted URL: $SHINE_DESKTOP_RELEASE_API_ORIGIN"
    echo "[INFO] Installer : $SHINE_DESKTOP_RELEASE_API_ORIGIN/api/desktop/installer"
    echo "[INFO] EXE build : data/desktop-installer/latest"
    npm run prod:desktop-web:release-exe
    ;;
  *)
    echo "[ERROR] Unknown option."
    exit 1
    ;;
esac

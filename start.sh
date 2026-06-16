#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

LOOPBACK_IPV4="127.0.0.1"
CLIENT_URL="http://${LOOPBACK_IPV4}:5000"
SERVER_URL="http://${LOOPBACK_IPV4}:5001"
DESKTOP_SHELL_URL="http://${LOOPBACK_IPV4}:5123"
DEFAULT_LOCATOR_CSV_URL="https://drive.google.com/uc?export=download&id=1K1YZVkPF42X2F5oA6_ZQYfrB57JHhxma"

export HOST="$LOOPBACK_IPV4"
export CLIENT_ORIGIN="$CLIENT_URL"
export DESKTOP_SHELL_ORIGIN="$DESKTOP_SHELL_URL"
export SERVER_ORIGIN="$SERVER_URL"
export SHINE_DESKTOP_DEV_URL="$CLIENT_URL"
export SHINE_DESKTOP_API_ORIGIN="$SERVER_URL"
export SHINE_DESKTOP_SHELL_HOST="$LOOPBACK_IPV4"
export SHINE_DESKTOP_LOCATOR_CSV_URL="${SHINE_DESKTOP_LOCATOR_CSV_URL:-$DEFAULT_LOCATOR_CSV_URL}"

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

load_release_env() {
  if [ -f desktop/.release-local.env ]; then
    # shellcheck disable=SC1091
    source desktop/.release-local.env
    echo "[INFO] Loaded local desktop signing env from desktop/.release-local.env"
    return 0
  fi
  return 1
}

ensure_release_env() {
  if load_release_env; then
    return 0
  fi
  read -r -p "Create a local self-signed desktop signing cert now? [Y/n]: " create_cert
  create_cert="${create_cert:-Y}"
  if [[ "$create_cert" =~ ^[Yy]$ ]]; then
    desktop/scripts/create-self-signed-cert.sh
    load_release_env || true
  fi
}

linux_signing_needs_legacy_crypto() {
  local signer
  signer="$HOME/.cache/electron-builder/winCodeSign/winCodeSign-2.6.0/linux/osslsigncode"
  [ -x "$signer" ] && ldd "$signer" 2>/dev/null | grep -q 'libcrypto.so.1.1 => not found'
}

prepare_desktop_release_signing() {
  ensure_release_env
  if [ -n "${SHINE_DESKTOP_CERT_PATH:-}" ] && [ "$(uname -s)" = "Linux" ] && linux_signing_needs_legacy_crypto; then
    echo "[WARN] This Linux server cannot currently run electron-builder's bundled Windows signer."
    echo "[WARN] Missing library: libcrypto.so.1.1"
    echo "[WARN] You can still build/publish an unsigned EXE update feed for testing."
    read -r -p "Continue unsigned for this Linux test build? [Y/n]: " unsigned_ok
    unsigned_ok="${unsigned_ok:-Y}"
    if [[ "$unsigned_ok" =~ ^[Yy]$ ]]; then
      unset SHINE_DESKTOP_CERT_PATH
      unset SHINE_DESKTOP_CERT_PASSWORD
      echo "[INFO] Signing disabled for this run only."
    else
      echo "[ERROR] Install libcrypto.so.1.1 support or build/sign on Windows, then rerun."
      exit 1
    fi
  fi
}

print_desktop_release_urls() {
  echo
  echo "[SUCCESS] Desktop EXE/update artifacts are ready."
  echo "Installer page : $SHINE_DESKTOP_RELEASE_API_ORIGIN/api/desktop/installer"
  echo "Installer EXE  : $SHINE_DESKTOP_RELEASE_API_ORIGIN/api/desktop/installer/exe"
  echo "Updater feed   : $SHINE_DESKTOP_RELEASE_API_ORIGIN/api/desktop/updater/latest.yml"
  echo "Latest manifest: data/desktop-installer/latest/release.json"
  echo
  if [ -f data/desktop-installer/latest/latest.yml ]; then
    echo "[INFO] Current updater metadata:"
    sed -n '1,14p' data/desktop-installer/latest/latest.yml
  fi
}

if [ -f desktop/.release-local.env ]; then
  # shellcheck disable=SC1091
  load_release_env
fi

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
echo "  [6] Production VPS web + API (port 5000 + 5001)"
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
  echo "  [1] Local standalone EXE build only"
  echo "  [2] Smart hosted EXE/update channel (recommended)"
  read -r -p "Enter your choice [2]: " package_mode
  package_mode="${package_mode:-2}"
  default_origin="${SHINE_DESKTOP_RELEASE_API_ORIGIN:-https://rmkcetshine.me}"
  read -r -p "Enter Shine URL for packaged app [$default_origin]: " package_origin
  package_origin="${package_origin:-$default_origin}"
  package_origin="${package_origin%/}"
  export SHINE_DESKTOP_RELEASE_API_ORIGIN="$package_origin"
  export SHINE_DESKTOP_PUBLIC_BASE_URL="$package_origin"
  export SHINE_DESKTOP_RELEASE_CHANNEL_URL="$package_origin/api/desktop/installer"
  export SHINE_DESKTOP_UPDATER_FEED_URL="$package_origin/api/desktop/updater"
  export SHINE_DESKTOP_DOWNLOAD_PAGE_URL="$package_origin/api/desktop/installer"
  export SHINE_DESKTOP_PREFERRED_INSTALLER="exe"
  read -r -p "Enter public locator CSV URL (optional) [${SHINE_DESKTOP_LOCATOR_CSV_URL:-}]: " locator_csv
  if [ -n "$locator_csv" ]; then export SHINE_DESKTOP_LOCATOR_CSV_URL="$locator_csv"; fi
  read -r -p "Override release channel URL (optional) [$SHINE_DESKTOP_RELEASE_CHANNEL_URL]: " release_channel
  if [ -n "$release_channel" ]; then export SHINE_DESKTOP_RELEASE_CHANNEL_URL="$release_channel"; fi
  prepare_desktop_release_signing

  if [ "$package_mode" = "1" ]; then
    npm run desktop:exe
  else
    npm run desktop:release:exe
  fi
  print_desktop_release_urls
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
    default_origin="${SHINE_DESKTOP_RELEASE_API_ORIGIN:-https://rmkcetshine.me}"
    read -r -p "Enter hosted Shine server domain [$default_origin]: " package_origin
    package_origin="${package_origin:-$default_origin}"
    package_origin="${package_origin%/}"
    bind_host="${SHINE_SERVER_BIND_HOST:-0.0.0.0}"
    export HOST="$bind_host"
    export CLIENT_ORIGIN="$package_origin"
    export CLIENT_ORIGINS="$package_origin,http://127.0.0.1:5000,http://0.0.0.0:5000"
    export SERVER_ORIGIN="http://127.0.0.1:5001"
    export SHINE_DESKTOP_RELEASE_API_ORIGIN="$package_origin"
    export SHINE_DESKTOP_PUBLIC_BASE_URL="$package_origin"
    export SHINE_DESKTOP_RELEASE_CHANNEL_URL="$package_origin/api/desktop/installer"
    export SHINE_DESKTOP_UPDATER_FEED_URL="$package_origin/api/desktop/updater"
    export SHINE_DESKTOP_DOWNLOAD_PAGE_URL="$package_origin/api/desktop/installer"
    export SHINE_DESKTOP_PREFERRED_INSTALLER="exe"
    export SHINE_DESKTOP_SHELL_PORT="5123"
    export SHINE_DESKTOP_WAIT_FOR_PRIMARY="1"
    read -r -p "Enter public Google Sheet locator CSV URL (optional) [${SHINE_DESKTOP_LOCATOR_CSV_URL:-}]: " locator_csv
    if [ -n "$locator_csv" ]; then export SHINE_DESKTOP_LOCATOR_CSV_URL="$locator_csv"; fi
    prepare_desktop_release_signing
    echo "[INFO] Hosted URL: $SHINE_DESKTOP_RELEASE_API_ORIGIN"
    echo "[INFO] Bind host : $HOST"
    echo "[INFO] Web app   : http://$HOST:5000"
    echo "[INFO] API base  : http://$HOST:5001"
    echo "[INFO] Public web: $CLIENT_ORIGIN"
    echo "[INFO] Installer : $SHINE_DESKTOP_RELEASE_API_ORIGIN/api/desktop/installer/exe"
    echo "[INFO] Updates   : $SHINE_DESKTOP_RELEASE_API_ORIGIN/api/desktop/updater/latest.yml"
    echo "[INFO] Starting production web preview on port 5000 and API server on port 5001."
    npm run prod:web
    ;;
  *)
    echo "[ERROR] Unknown option."
    exit 1
    ;;
esac

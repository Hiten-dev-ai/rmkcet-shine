#!/usr/bin/env bash
set -euo pipefail

APP_DIR="${APP_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)}"
SERVICE_NAME="${SERVICE_NAME:-rmkcet-shine}"
APP_USER="${APP_USER:-${SUDO_USER:-$USER}}"
APP_GROUP="${APP_GROUP:-$(id -gn "$APP_USER")}"
APP_HOST="${APP_HOST:-::}"
APP_PORT="${APP_PORT:-5000}"
DEFAULT_IP="$(hostname -I 2>/dev/null | awk '{print $1}')"
APP_ORIGIN="${APP_ORIGIN:-http://${DEFAULT_IP:-127.0.0.1}:${APP_PORT}}"
ENV_FILE="${ENV_FILE:-$APP_DIR/.env}"
SERVICE_FILE="/etc/systemd/system/${SERVICE_NAME}.service"

if [[ "${EUID}" -ne 0 ]]; then
  echo "Please run install.sh as root or with sudo."
  exit 1
fi

log() {
  printf '\n[rmkcet-shine] %s\n' "$1"
}

run_as_app_user() {
  if [[ "$APP_USER" == "root" ]]; then
    "$@"
  else
    runuser -u "$APP_USER" -- "$@"
  fi
}

upsert_env() {
  local key="$1"
  local value="$2"
  if grep -qE "^${key}=" "$ENV_FILE" 2>/dev/null; then
    sed -i "s|^${key}=.*|${key}=${value}|" "$ENV_FILE"
  else
    printf '%s=%s\n' "$key" "$value" >> "$ENV_FILE"
  fi
}

install_base_packages() {
  log "Installing Ubuntu dependencies"
  apt-get update
  apt-get install -y curl ca-certificates gnupg git build-essential python3 python3-pip python3-venv rsync
}

install_nodejs() {
  if command -v node >/dev/null 2>&1; then
    local current_major
    current_major="$(node -p 'process.versions.node.split(".")[0]')"
    if [[ "${current_major}" -ge 20 ]]; then
      log "Node.js $(node -v) already satisfies the requirement"
      return
    fi
  fi

  log "Installing Node.js 22.x"
  mkdir -p /etc/apt/keyrings
  curl -fsSL https://deb.nodesource.com/gpgkey/nodesource-repo.gpg.key | gpg --dearmor -o /etc/apt/keyrings/nodesource.gpg
  echo "deb [signed-by=/etc/apt/keyrings/nodesource.gpg] https://deb.nodesource.com/node_22.x nodistro main" > /etc/apt/sources.list.d/nodesource.list
  apt-get update
  apt-get install -y nodejs
}

prepare_directories() {
  log "Preparing runtime directories"
  mkdir -p "$APP_DIR/data/backups" "$APP_DIR/data/archives" "$APP_DIR/data/notice_assets" "$APP_DIR/logs"
  chown -R "$APP_USER:$APP_GROUP" "$APP_DIR"
}

prepare_env_file() {
  log "Preparing environment file"
  touch "$ENV_FILE"
  upsert_env "HOST" "$APP_HOST"
  upsert_env "PORT" "$APP_PORT"
  upsert_env "CLIENT_ORIGIN" "$APP_ORIGIN"
  upsert_env "SERVER_ORIGIN" "$APP_ORIGIN"
  upsert_env "SHINE_DB_PATH" "$APP_DIR/data/rmkcet.db"
}

install_app_dependencies() {
  log "Installing npm dependencies"
  run_as_app_user npm --prefix "$APP_DIR" install
  run_as_app_user npm --prefix "$APP_DIR/client" install
  run_as_app_user npm --prefix "$APP_DIR/server" install
}

build_app() {
  log "Building production assets"
  run_as_app_user npm --prefix "$APP_DIR" run build
}

install_service() {
  log "Installing systemd service"
  cat > "$SERVICE_FILE" <<SERVICE
[Unit]
Description=RMKCET Shine
After=network-online.target
Wants=network-online.target

[Service]
Type=simple
User=${APP_USER}
Group=${APP_GROUP}
WorkingDirectory=${APP_DIR}
EnvironmentFile=-${ENV_FILE}
Environment=NODE_ENV=production
Environment=HOST=${APP_HOST}
Environment=PORT=${APP_PORT}
Environment=CLIENT_ORIGIN=${APP_ORIGIN}
Environment=SERVER_ORIGIN=${APP_ORIGIN}
Environment=SHINE_DB_PATH=${APP_DIR}/data/rmkcet.db
ExecStart=/usr/bin/env node ${APP_DIR}/server/dist/index.js
Restart=always
RestartSec=5
StandardOutput=append:${APP_DIR}/logs/server.log
StandardError=append:${APP_DIR}/logs/server-error.log

[Install]
WantedBy=multi-user.target
SERVICE

  systemctl daemon-reload
  systemctl enable --now "$SERVICE_NAME"
}

print_summary() {
  log "Installation complete"
  echo "Service name : $SERVICE_NAME"
  echo "App directory : $APP_DIR"
  echo "App origin    : $APP_ORIGIN"
  echo "Check status  : systemctl status $SERVICE_NAME"
  echo "View logs     : journalctl -u $SERVICE_NAME -f"
}

install_base_packages
install_nodejs
prepare_directories
prepare_env_file
install_app_dependencies
build_app
install_service
print_summary

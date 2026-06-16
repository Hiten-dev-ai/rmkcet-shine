#!/usr/bin/env bash
set -euo pipefail

DOMAIN="${DOMAIN:-rmkcetshine.me}"
UPSTREAM_HOST="${UPSTREAM_HOST:-127.0.0.1}"
UPSTREAM_PORT="${UPSTREAM_PORT:-5000}"
UPSTREAM_SCHEME="${UPSTREAM_SCHEME:-http}"
WEBROOT="/var/www/certbot"
NGINX_SITE="/etc/nginx/sites-available/${DOMAIN}"
EMAIL="${CERTBOT_EMAIL:-}"

if [[ -z "${EMAIL}" ]]; then
  echo "Set CERTBOT_EMAIL before running this script, for example:"
  echo "  CERTBOT_EMAIL=admin@${DOMAIN} $0"
  exit 1
fi

sudo apt-get update
sudo apt-get install -y nginx certbot

sudo mkdir -p "${WEBROOT}"

write_http_site() {
  cat <<EOF | sudo tee "${NGINX_SITE}" >/dev/null
server {
    listen 80;
    listen [::]:80;

    server_name ${DOMAIN};

    location ^~ /.well-known/acme-challenge/ {
        root ${WEBROOT};
        default_type "text/plain";
        try_files \$uri =404;
    }

    location / {
        proxy_pass ${UPSTREAM_SCHEME}://${UPSTREAM_HOST}:${UPSTREAM_PORT};
        proxy_http_version 1.1;
        proxy_set_header Host \$host;
        proxy_set_header X-Real-IP \$remote_addr;
        proxy_set_header X-Forwarded-For \$proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto \$scheme;
        proxy_set_header X-Forwarded-Host \$host;
        proxy_set_header X-Forwarded-Port 80;
        proxy_read_timeout 60s;
        proxy_send_timeout 60s;
EOF

  if [[ "${UPSTREAM_SCHEME}" == "https" ]]; then
    cat <<'EOF' | sudo tee -a "${NGINX_SITE}" >/dev/null
        proxy_ssl_server_name on;
        proxy_ssl_verify off;
EOF
  fi

  cat <<'EOF' | sudo tee -a "${NGINX_SITE}" >/dev/null
    }
}
EOF
}

write_https_site() {
  cat <<EOF | sudo tee "${NGINX_SITE}" >/dev/null
server {
    listen 80;
    listen [::]:80;

    server_name ${DOMAIN};

    location ^~ /.well-known/acme-challenge/ {
        root ${WEBROOT};
        default_type "text/plain";
        try_files \$uri =404;
    }

    location / {
        return 301 https://\$host\$request_uri;
    }
}

server {
    listen 443 ssl http2;
    listen [::]:443 ssl http2;

    server_name ${DOMAIN};

    ssl_certificate /etc/letsencrypt/live/${DOMAIN}/fullchain.pem;
    ssl_certificate_key /etc/letsencrypt/live/${DOMAIN}/privkey.pem;
    ssl_trusted_certificate /etc/letsencrypt/live/${DOMAIN}/chain.pem;

    ssl_protocols TLSv1.2 TLSv1.3;
    ssl_prefer_server_ciphers off;
    ssl_session_cache shared:SSL:10m;
    ssl_session_timeout 1d;

    location / {
        proxy_pass ${UPSTREAM_SCHEME}://${UPSTREAM_HOST}:${UPSTREAM_PORT};
        proxy_http_version 1.1;
        proxy_set_header Host \$host;
        proxy_set_header X-Real-IP \$remote_addr;
        proxy_set_header X-Forwarded-For \$proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto https;
        proxy_set_header X-Forwarded-Host \$host;
        proxy_set_header X-Forwarded-Port 443;
        proxy_read_timeout 60s;
        proxy_send_timeout 60s;
EOF

  if [[ "${UPSTREAM_SCHEME}" == "https" ]]; then
    cat <<'EOF' | sudo tee -a "${NGINX_SITE}" >/dev/null
        proxy_ssl_server_name on;
        proxy_ssl_verify off;
EOF
  fi

  cat <<'EOF' | sudo tee -a "${NGINX_SITE}" >/dev/null
    }
}
EOF
}

write_http_site
sudo ln -sf "${NGINX_SITE}" "/etc/nginx/sites-enabled/${DOMAIN}"
sudo nginx -t
sudo systemctl reload nginx

sudo certbot certonly \
  --webroot \
  -w "${WEBROOT}" \
  -d "${DOMAIN}" \
  --agree-tos \
  --no-eff-email \
  -m "${EMAIL}"

write_https_site
sudo nginx -t
sudo systemctl reload nginx

echo "Done. A renewal dry-run is available with:"
echo "  sudo certbot renew --dry-run"

# Nginx and Certbot Setup

This repo includes a reverse-proxy setup script for `rmkcetshine.me` and can be reused for a subdomain like `meet.rmkcetshine.me`.

## Assumptions

- The upstream app is reachable on an IPv4 address and port you control.
- DNS for `meet.rmkcetshine.me` points at this nginx host.
- Ports `80` and `443` are open in the firewall and on the cloud/security group.
- If you are proxying TrueConf Server for browser/web access, the backend should also have its client port available, usually `4307`.

For TrueConf Server in this setup, the upstream web manager is plain HTTP on `8443`, so use `UPSTREAM_SCHEME=http`.

## Files

- `deploy/setup-nginx-certbot.sh` installs nginx/certbot, issues the cert with the webroot method, and rewrites the nginx site for HTTPS.

## Run

```bash
chmod +x deploy/setup-nginx-certbot.sh
DOMAIN=meet.rmkcetshine.me \
UPSTREAM_HOST=10.0.0.25 \
UPSTREAM_PORT=8443 \
UPSTREAM_SCHEME=http \
CERTBOT_EMAIL=admin@rmkcetshine.me \
deploy/setup-nginx-certbot.sh
```

## Renewal

Certbot installs a systemd timer on Ubuntu-based systems. Verify it with:

```bash
sudo certbot renew --dry-run
```

## Notes

- The ACME challenge path is served from `/var/www/certbot`, which keeps renewals working even after the redirect to HTTPS is enabled.
- nginx must be reloaded after any config change:

```bash
sudo nginx -t && sudo systemctl reload nginx
```

## Azure Ports

For a standard TrueConf Server deployment behind nginx, open:

- `80/tcp` for Certbot HTTP validation and redirect traffic
- `443/tcp` for the nginx HTTPS site
- `4307/tcp` for TrueConf client signaling and media

If you are using TrueConf Server Free and need to register the server, allow outbound `4310/tcp` to `reg.trueconf.com`.
If you enable WebRTC, also allow the configured WebRTC range, which is `53000-56000/tcp` and `53000-56000/udp` by default.

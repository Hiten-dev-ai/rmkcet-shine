const { app, shell } = require('electron');
const { existsSync, mkdirSync } = require('node:fs');
const path = require('node:path');

const appId = process.env.SHINE_DESKTOP_APP_ID || 'RMKCET.Shine.App';
const displayName = 'RMKCET Shine';
const desktopRoot = path.resolve(__dirname, '..');
const repoRoot = path.resolve(desktopRoot, '..');
const target = path.resolve(desktopRoot, 'node_modules', 'electron', 'dist', 'RMKCET Shine Dev.exe');
const icon = path.resolve(desktopRoot, 'assets', 'icon.ico');

app.whenReady().then(() => {
  const shortcuts = [
    path.join(app.getPath('appData'), 'Microsoft', 'Windows', 'Start Menu', 'Programs', `${displayName}.lnk`),
    path.join(app.getPath('appData'), 'Microsoft', 'Windows', 'Start Menu', 'Programs', displayName, `${displayName}.lnk`),
  ];

  for (const shortcutPath of shortcuts) {
    mkdirSync(path.dirname(shortcutPath), { recursive: true });
    shell.writeShortcutLink(shortcutPath, existsSync(shortcutPath) ? 'update' : 'create', {
      target,
      cwd: desktopRoot,
      args: '.',
      description: displayName,
      icon,
      iconIndex: 0,
      appUserModelId: appId,
    });
    console.log(`${shortcutPath} -> ${appId}`);
  }

  const badShortcut = path.join(app.getPath('appData'), 'Microsoft', 'Windows', 'Start Menu', 'Programs', 'Electron.lnk');
  if (existsSync(badShortcut)) {
    try {
      const bad = shell.readShortcutLink(badShortcut);
      if (String(bad.target || '').toLowerCase().startsWith(path.resolve(desktopRoot, 'node_modules', 'electron', 'dist').toLowerCase())) {
        require('node:fs').unlinkSync(badShortcut);
        console.log(`removed ${badShortcut}`);
      }
    } catch {
      // Ignore unreadable shortcut cleanup.
    }
  }

  app.exit(0);
});

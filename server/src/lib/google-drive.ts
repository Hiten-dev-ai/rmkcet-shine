import { getAppConfig } from './db.js';

export const GOOGLE_DRIVE_SCOPE = 'https://www.googleapis.com/auth/drive';
const DRIVE_FOLDER_MIME = 'application/vnd.google-apps.folder';

export interface GoogleDriveSettings {
  enabled: boolean;
  clientId: string;
  clientSecret: string;
  refreshToken: string;
  folderId: string;
}

export interface GoogleDriveFileRecord {
  id: string;
  name: string;
  size_kb: number;
  modified: string;
}

export interface GoogleDriveEntryRecord extends GoogleDriveFileRecord {
  mimeType: string;
  isFolder: boolean;
}

interface GoogleDriveApiFile {
  id?: string;
  name?: string;
  size?: string;
  modifiedTime?: string;
  mimeType?: string;
}

function mapDriveEntry(file: GoogleDriveApiFile): GoogleDriveEntryRecord | null {
  const id = String(file.id || '');
  const name = String(file.name || '');
  if (!id || !name) return null;
  const mimeType = String(file.mimeType || '');
  return {
    id,
    name,
    size_kb: Math.floor(Number(file.size || 0) / 1024),
    modified: String(file.modifiedTime || '').slice(0, 16).replace('T', ' '),
    mimeType,
    isFolder: mimeType === DRIVE_FOLDER_MIME,
  };
}

export function getGoogleDriveSettings(config = getAppConfig()): GoogleDriveSettings {
  const clientId = String(config.google_oauth_client_id || '').trim();
  const clientSecret = String(config.google_oauth_client_secret || '').trim();
  const refreshToken = String(config.google_drive_refresh_token || '').trim();
  const folderId = String(config.google_drive_folder_id || '').trim();
  return {
    enabled: !!(clientId && clientSecret && refreshToken),
    clientId,
    clientSecret,
    refreshToken,
    folderId,
  };
}

function escapeDriveQueryValue(value: string) {
  return String(value || '').replace(/\\/g, '\\\\').replace(/'/g, "\\'");
}

async function getAccessToken(settings = getGoogleDriveSettings()) {
  if (!settings.enabled) {
    throw new Error('Google Drive backup mode is not configured. Add Google OAuth client ID, client secret, and Drive refresh token in settings.');
  }

  const response = await fetch('https://oauth2.googleapis.com/token', {
    method: 'POST',
    headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
    body: new URLSearchParams({
      client_id: settings.clientId,
      client_secret: settings.clientSecret,
      refresh_token: settings.refreshToken,
      grant_type: 'refresh_token',
    }).toString(),
  });

  const payload = await response.json().catch(() => ({}));
  if (!response.ok || !payload.access_token) {
    throw new Error(String(payload.error_description || payload.error || 'Failed to refresh Google Drive access token.'));
  }
  return String(payload.access_token);
}

async function driveJson<T>(url: string, init: RequestInit = {}, settings = getGoogleDriveSettings()): Promise<T> {
  const accessToken = await getAccessToken(settings);
  const response = await fetch(url, {
    ...init,
    headers: {
      Authorization: `Bearer ${accessToken}`,
      ...(init.headers || {}),
    },
  });
  const payload = await response.json().catch(() => ({}));
  if (!response.ok) {
    throw new Error(String((payload as { error?: { message?: string } })?.error?.message || 'Google Drive request failed.'));
  }
  return payload as T;
}

async function driveBuffer(url: string, settings = getGoogleDriveSettings()) {
  const accessToken = await getAccessToken(settings);
  const response = await fetch(url, {
    headers: {
      Authorization: `Bearer ${accessToken}`,
    },
  });
  if (!response.ok) {
    const payload = await response.json().catch(() => ({}));
    throw new Error(String((payload as { error?: { message?: string } })?.error?.message || 'Google Drive download failed.'));
  }
  return Buffer.from(await response.arrayBuffer());
}

export async function listDriveFiles(namePrefixes: string[] = [], settings = getGoogleDriveSettings()) {
  const filters = [`trashed = false`, `mimeType != 'application/vnd.google-apps.folder'`];
  if (settings.folderId) {
    filters.push(`'${escapeDriveQueryValue(settings.folderId)}' in parents`);
  }
  if (namePrefixes.length) {
    const clause = namePrefixes
      .map((prefix) => `name contains '${escapeDriveQueryValue(prefix)}'`)
      .join(' or ');
    filters.push(`(${clause})`);
  }
  const q = filters.join(' and ');
  const url = `https://www.googleapis.com/drive/v3/files?${new URLSearchParams({
    q,
    fields: 'files(id,name,size,modifiedTime,mimeType)',
    pageSize: '1000',
    supportsAllDrives: 'false',
    includeItemsFromAllDrives: 'false',
  }).toString()}`;
  const payload = await driveJson<{ files?: GoogleDriveApiFile[] }>(url, {}, settings);
  return (payload.files || []).map(mapDriveEntry).filter((file): file is GoogleDriveEntryRecord => !!file);
}

export async function findDriveFilesByName(name: string, settings = getGoogleDriveSettings()) {
  const filters = [
    `trashed = false`,
    `mimeType != 'application/vnd.google-apps.folder'`,
    `name = '${escapeDriveQueryValue(name)}'`,
  ];
  if (settings.folderId) {
    filters.push(`'${escapeDriveQueryValue(settings.folderId)}' in parents`);
  }
  const url = `https://www.googleapis.com/drive/v3/files?${new URLSearchParams({
    q: filters.join(' and '),
    fields: 'files(id,name,size,modifiedTime,mimeType)',
    pageSize: '100',
  }).toString()}`;
  return driveJson<{ files?: GoogleDriveApiFile[] }>(url, {}, settings).then((payload) =>
    (payload.files || []).map(mapDriveEntry).filter((file): file is GoogleDriveEntryRecord => !!file),
  );
}

export async function uploadDriveFile(params: {
  name: string;
  mimeType: string;
  content: Buffer;
  parentId?: string;
  overwrite?: boolean;
}, settings = getGoogleDriveSettings()) {
  const existing = params.parentId
    ? await findDriveFilesByNameInParent(params.name, params.parentId, settings)
    : await findDriveFilesByName(params.name, settings);
  if (existing.length && !params.overwrite) {
    throw new Error(`A Google Drive backup named "${params.name}" already exists. Enable overwrite to replace it.`);
  }
  if (existing.length && params.overwrite) {
    for (const file of existing) {
      await deleteDriveFile(file.id, settings);
    }
  }

  const accessToken = await getAccessToken(settings);
  const metadata: Record<string, unknown> = {
    name: params.name,
  };
  if (params.parentId || settings.folderId) {
    metadata.parents = [params.parentId || settings.folderId];
  }

  const startResponse = await fetch('https://www.googleapis.com/upload/drive/v3/files?uploadType=resumable&fields=id,name,size,modifiedTime', {
    method: 'POST',
    headers: {
      Authorization: `Bearer ${accessToken}`,
      'Content-Type': 'application/json; charset=UTF-8',
      'X-Upload-Content-Type': params.mimeType,
      'X-Upload-Content-Length': String(params.content.length),
    },
    body: JSON.stringify(metadata),
  });
  if (!startResponse.ok) {
    const payload = await startResponse.json().catch(() => ({}));
    throw new Error(String((payload as { error?: { message?: string } })?.error?.message || 'Unable to initialize Google Drive upload.'));
  }

  const uploadUrl = startResponse.headers.get('location');
  if (!uploadUrl) {
    throw new Error('Google Drive upload session did not return a resumable upload URL.');
  }

  const finishResponse = await fetch(uploadUrl, {
    method: 'PUT',
    headers: {
      'Content-Type': params.mimeType,
      'Content-Length': String(params.content.length),
    },
    body: new Uint8Array(params.content),
  });
  const payload = await finishResponse.json().catch(() => ({}));
  if (!finishResponse.ok) {
    throw new Error(String((payload as { error?: { message?: string } })?.error?.message || 'Google Drive upload failed.'));
  }
  return payload as { id?: string; name?: string; size?: string; modifiedTime?: string };
}

export async function downloadDriveFileById(fileId: string, settings = getGoogleDriveSettings()) {
  return driveBuffer(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(fileId)}?alt=media`, settings);
}

export async function downloadDriveFileByName(name: string, settings = getGoogleDriveSettings()) {
  const matches = await findDriveFilesByName(name, settings);
  if (!matches.length) {
    throw new Error(`Google Drive file "${name}" was not found.`);
  }
  return downloadDriveFileById(matches[0].id, settings);
}

export async function deleteDriveFile(fileId: string, settings = getGoogleDriveSettings()) {
  const accessToken = await getAccessToken(settings);
  const response = await fetch(`https://www.googleapis.com/drive/v3/files/${encodeURIComponent(fileId)}`, {
    method: 'DELETE',
    headers: {
      Authorization: `Bearer ${accessToken}`,
    },
  });
  if (!response.ok) {
    const payload = await response.json().catch(() => ({}));
    throw new Error(String((payload as { error?: { message?: string } })?.error?.message || 'Failed to delete Google Drive file.'));
  }
}

export async function deleteDriveFileByName(name: string, settings = getGoogleDriveSettings()) {
  const matches = await findDriveFilesByName(name, settings);
  if (!matches.length) {
    throw new Error(`Google Drive file "${name}" was not found.`);
  }
  for (const file of matches) {
    await deleteDriveFile(file.id, settings);
  }
}

export async function findDriveFilesByNameInParent(name: string, parentId: string, settings = getGoogleDriveSettings()) {
  const filters = [
    `trashed = false`,
    `name = '${escapeDriveQueryValue(name)}'`,
    `'${escapeDriveQueryValue(parentId)}' in parents`,
  ];
  const url = `https://www.googleapis.com/drive/v3/files?${new URLSearchParams({
    q: filters.join(' and '),
    fields: 'files(id,name,size,modifiedTime,mimeType)',
    pageSize: '100',
  }).toString()}`;
  return driveJson<{ files?: GoogleDriveApiFile[] }>(url, {}, settings).then((payload) =>
    (payload.files || []).map(mapDriveEntry).filter((file): file is GoogleDriveEntryRecord => !!file),
  );
}

export async function listDriveEntriesInParent(parentId: string, settings = getGoogleDriveSettings()) {
  const filters = [
    `trashed = false`,
    `'${escapeDriveQueryValue(parentId)}' in parents`,
  ];
  const url = `https://www.googleapis.com/drive/v3/files?${new URLSearchParams({
    q: filters.join(' and '),
    fields: 'files(id,name,size,modifiedTime,mimeType)',
    pageSize: '1000',
  }).toString()}`;
  return driveJson<{ files?: GoogleDriveApiFile[] }>(url, {}, settings).then((payload) =>
    (payload.files || []).map(mapDriveEntry).filter((file): file is GoogleDriveEntryRecord => !!file),
  );
}

export async function ensureDriveFolder(name: string, parentId: string, settings = getGoogleDriveSettings()) {
  const existing = await findDriveFilesByNameInParent(name, parentId, settings);
  const match = existing.find((file) => file.mimeType === DRIVE_FOLDER_MIME);
  if (match) return match.id;

  const accessToken = await getAccessToken(settings);
  const response = await fetch('https://www.googleapis.com/drive/v3/files?fields=id,name,mimeType', {
    method: 'POST',
    headers: {
      Authorization: `Bearer ${accessToken}`,
      'Content-Type': 'application/json; charset=UTF-8',
    },
    body: JSON.stringify({
      name,
      mimeType: DRIVE_FOLDER_MIME,
      parents: [parentId],
    }),
  });
  const payload = await response.json().catch(() => ({}));
  if (!response.ok || !payload.id) {
    throw new Error(String((payload as { error?: { message?: string } })?.error?.message || `Failed to create Drive folder "${name}".`));
  }
  return String(payload.id);
}

export async function ensureDrivePath(pathSegments: string[], settings = getGoogleDriveSettings()) {
  if (!settings.folderId) {
    throw new Error('Google Drive folder ID is required when Drive storage mode is enabled.');
  }
  let currentParentId = settings.folderId;
  for (const segment of pathSegments) {
    const clean = String(segment || '').trim();
    if (!clean) continue;
    currentParentId = await ensureDriveFolder(clean, currentParentId, settings);
  }
  return currentParentId;
}

export async function findDrivePath(pathSegments: string[], settings = getGoogleDriveSettings()) {
  if (!settings.folderId) {
    throw new Error('Google Drive folder ID is required when Drive storage mode is enabled.');
  }
  let currentParentId = settings.folderId;
  for (const segment of pathSegments) {
    const clean = String(segment || '').trim();
    if (!clean) continue;
    const entries = await findDriveFilesByNameInParent(clean, currentParentId, settings);
    const folder = entries.find((entry) => entry.isFolder);
    if (!folder) return null;
    currentParentId = folder.id;
  }
  return currentParentId;
}

export async function listDriveFilesInPath(pathSegments: string[] = [], settings = getGoogleDriveSettings()) {
  const parentId = pathSegments.length ? await ensureDrivePath(pathSegments, settings) : settings.folderId;
  if (!parentId) return [];
  const filters = [
    `trashed = false`,
    `mimeType != '${DRIVE_FOLDER_MIME}'`,
    `'${escapeDriveQueryValue(parentId)}' in parents`,
  ];
  const url = `https://www.googleapis.com/drive/v3/files?${new URLSearchParams({
    q: filters.join(' and '),
    fields: 'files(id,name,size,modifiedTime,mimeType)',
    pageSize: '1000',
  }).toString()}`;
  const payload = await driveJson<{ files?: GoogleDriveApiFile[] }>(url, {}, settings);
  return (payload.files || []).map(mapDriveEntry).filter((file): file is GoogleDriveEntryRecord => !!file);
}

export async function listDriveEntriesInPath(pathSegments: string[] = [], settings = getGoogleDriveSettings()) {
  const parentId = pathSegments.length ? await findDrivePath(pathSegments, settings) : settings.folderId;
  if (!parentId) return [];
  return listDriveEntriesInParent(parentId, settings);
}

export async function uploadDriveFileToPath(params: {
  pathSegments?: string[];
  name: string;
  mimeType: string;
  content: Buffer;
  overwrite?: boolean;
}, settings = getGoogleDriveSettings()) {
  const parentId = params.pathSegments?.length ? await ensureDrivePath(params.pathSegments, settings) : settings.folderId;
  return uploadDriveFile({
    name: params.name,
    mimeType: params.mimeType,
    content: params.content,
    parentId,
    overwrite: params.overwrite,
  }, settings);
}

export async function downloadDriveFileFromPath(pathSegments: string[] = [], name: string, settings = getGoogleDriveSettings()) {
  const parentId = pathSegments.length ? await ensureDrivePath(pathSegments, settings) : settings.folderId;
  if (!parentId) throw new Error('Google Drive folder ID is required.');
  const matches = await findDriveFilesByNameInParent(name, parentId, settings);
  if (!matches.length) throw new Error(`Google Drive file "${name}" was not found.`);
  return downloadDriveFileById(matches[0].id, settings);
}

export async function deleteDriveFileFromPath(pathSegments: string[] = [], name: string, settings = getGoogleDriveSettings()) {
  const parentId = pathSegments.length ? await ensureDrivePath(pathSegments, settings) : settings.folderId;
  if (!parentId) throw new Error('Google Drive folder ID is required.');
  const matches = await findDriveFilesByNameInParent(name, parentId, settings);
  if (!matches.length) throw new Error(`Google Drive file "${name}" was not found.`);
  for (const file of matches) {
    await deleteDriveFile(file.id, settings);
  }
}

async function deleteDriveEntryRecursive(entry: GoogleDriveEntryRecord, settings = getGoogleDriveSettings()) {
  if (entry.isFolder) {
    const children = await listDriveEntriesInParent(entry.id, settings);
    for (const child of children) {
      await deleteDriveEntryRecursive(child, settings);
    }
  }
  await deleteDriveFile(entry.id, settings);
}

export async function clearDrivePath(pathSegments: string[] = [], settings = getGoogleDriveSettings()) {
  const parentId = pathSegments.length ? await findDrivePath(pathSegments, settings) : settings.folderId;
  if (!parentId) return;
  const entries = await listDriveEntriesInParent(parentId, settings);
  for (const entry of entries) {
    await deleteDriveEntryRecursive(entry, settings);
  }
}

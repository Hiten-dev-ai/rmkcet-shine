type CacheEntry<T> = {
  timestamp: number;
  payload: T;
};

type CacheBucketRecord<T> = Record<string, CacheEntry<T>>;

const CACHE_PREFIX = 'shine-read-model-cache-v3';
const MAX_BUCKET_ENTRIES = 24;

function getStorageKey(namespace: string, bucket: string) {
  return `${CACHE_PREFIX}::${namespace}::${bucket}`;
}

function readBucket<T>(namespace: string, bucket: string): CacheBucketRecord<T> {
  if (!namespace || typeof window === 'undefined') return {};
  try {
    const raw = window.localStorage.getItem(getStorageKey(namespace, bucket));
    if (!raw) return {};
    const parsed = JSON.parse(raw) as CacheBucketRecord<T>;
    return parsed && typeof parsed === 'object' ? parsed : {};
  } catch {
    return {};
  }
}

function writeBucket<T>(namespace: string, bucket: string, record: CacheBucketRecord<T>) {
  if (!namespace || typeof window === 'undefined') return;
  try {
    window.localStorage.setItem(getStorageKey(namespace, bucket), JSON.stringify(record));
  } catch {
    // Ignore persistent cache failures.
  }
}

export function readPersistentCacheEntry<T>(namespace: string, bucket: string, key: string): CacheEntry<T> | null {
  const record = readBucket<T>(namespace, bucket);
  return record[key] || null;
}

export function writePersistentCacheEntry<T>(
  namespace: string,
  bucket: string,
  key: string,
  entry: CacheEntry<T>,
) {
  const record = readBucket<T>(namespace, bucket);
  record[key] = entry;
  const ordered = Object.entries(record)
    .sort((a, b) => Number(b[1]?.timestamp || 0) - Number(a[1]?.timestamp || 0))
    .slice(0, MAX_BUCKET_ENTRIES);
  writeBucket(namespace, bucket, Object.fromEntries(ordered));
}

export function clearPersistentCacheBucket(namespace: string, bucket: string) {
  if (!namespace || typeof window === 'undefined') return;
  try {
    window.localStorage.removeItem(getStorageKey(namespace, bucket));
  } catch {
    // Ignore persistent cache cleanup failures.
  }
}

export function seedPersistentCacheEntries<T>(
  namespace: string,
  bucket: string,
  entries: Array<{ key: string; entry: CacheEntry<T> }>,
) {
  if (!entries.length) return;
  const record = readBucket<T>(namespace, bucket);
  for (const item of entries) {
    if (!item?.key) continue;
    record[item.key] = item.entry;
  }
  const ordered = Object.entries(record)
    .sort((a, b) => Number(b[1]?.timestamp || 0) - Number(a[1]?.timestamp || 0))
    .slice(0, MAX_BUCKET_ENTRIES);
  writeBucket(namespace, bucket, Object.fromEntries(ordered));
}

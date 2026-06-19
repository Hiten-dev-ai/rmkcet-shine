export type PerformanceEventStatus = 'ok' | 'error';

export type PerformanceEvent = {
  area: string;
  name: string;
  durationMs: number;
  status: PerformanceEventStatus;
  meta?: Record<string, string | number | boolean>;
};

const MAX_PERFORMANCE_EVENTS = 150;
const performanceEvents: PerformanceEvent[] = [];

function nowMs() {
  return typeof performance !== 'undefined' ? performance.now() : Date.now();
}

export function recordPerformanceEvent(event: PerformanceEvent) {
  performanceEvents.push({
    ...event,
    durationMs: Math.max(0, Math.round(event.durationMs)),
  });
  if (performanceEvents.length > MAX_PERFORMANCE_EVENTS) {
    performanceEvents.splice(0, performanceEvents.length - MAX_PERFORMANCE_EVENTS);
  }
  if (import.meta.env.DEV && event.durationMs >= 250) {
    console.info(`[perf] ${event.area}:${event.name} ${Math.round(event.durationMs)}ms ${event.status}`, event.meta || {});
  }
}

export async function measureAsync<T>(
  area: string,
  name: string,
  fn: () => Promise<T>,
  meta?: PerformanceEvent['meta'],
) {
  const startedAt = nowMs();
  try {
    const value = await fn();
    recordPerformanceEvent({ area, name, durationMs: nowMs() - startedAt, status: 'ok', meta });
    return value;
  } catch (error) {
    recordPerformanceEvent({ area, name, durationMs: nowMs() - startedAt, status: 'error', meta });
    throw error;
  }
}

export function getPerformanceEvents() {
  return [...performanceEvents];
}

export function getPerformanceSummary() {
  const buckets = new Map<string, { count: number; totalMs: number; maxMs: number; errors: number }>();
  for (const event of performanceEvents) {
    const key = `${event.area}:${event.name}`;
    const bucket = buckets.get(key) || { count: 0, totalMs: 0, maxMs: 0, errors: 0 };
    bucket.count += 1;
    bucket.totalMs += event.durationMs;
    bucket.maxMs = Math.max(bucket.maxMs, event.durationMs);
    if (event.status === 'error') bucket.errors += 1;
    buckets.set(key, bucket);
  }
  return Array.from(buckets.entries())
    .map(([key, bucket]) => ({
      key,
      count: bucket.count,
      avgMs: Math.round(bucket.totalMs / Math.max(1, bucket.count)),
      maxMs: Math.round(bucket.maxMs),
      errors: bucket.errors,
    }))
    .sort((left, right) => right.maxMs - left.maxMs);
}

declare global {
  interface Window {
    __SHINE_PERFORMANCE_EVENTS__?: typeof getPerformanceEvents;
    __SHINE_PERFORMANCE_SUMMARY__?: typeof getPerformanceSummary;
  }
}

if (typeof window !== 'undefined') {
  window.__SHINE_PERFORMANCE_EVENTS__ = getPerformanceEvents;
  window.__SHINE_PERFORMANCE_SUMMARY__ = getPerformanceSummary;
}

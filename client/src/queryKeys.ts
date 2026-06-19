export const queryKeys = {
  bootstrap: ['bootstrap'] as const,
  dashboard: (scope = 'default') => ['dashboard', scope] as const,
  reports: (scope = 'default') => ['reports', scope] as const,
  activity: (scope = 'default') => ['activity', scope] as const,
  cdp: (scope = 'default') => ['cdp', scope] as const,
  users: (scope = 'default') => ['users', scope] as const,
  notices: (scope = 'default') => ['notices', scope] as const,
  notifications: (email: string) => ['notifications', String(email || '').trim().toLowerCase()] as const,
  sendPage: (kind: 'report' | 'notice', id: string | number, mode = 'app') => ['sendPage', kind, String(id), mode] as const,
};

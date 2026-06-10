export type Role = 'admin' | 'principal' | 'hod' | 'deo' | 'counselor';

export interface ScopeRow {
  department: string;
  year_level: number;
}

export interface AuthUser {
  email: string;
  name: string;
  role: Role;
  department: string | null;
  year_level: number;
  scopes: ScopeRow[];
}

export function normalizeRole(role: unknown): Role {
  const value = String(role || '').trim().toLowerCase();
  if (value === 'principal') return 'principal';
  if (value === 'hod' || value === 'chief_admin') return 'hod';
  if (value === 'deo') return 'deo';
  if (value === 'counselor') return 'counselor';
  return 'admin';
}

export function isAdminPortalRole(role: Role) {
  return role === 'admin' || role === 'principal' || role === 'hod' || role === 'deo';
}

export function allowedTabsForRole(role: Role) {
  if (role === 'admin') {
    return ['dashboard', 'reports', 'notices', 'departments', 'activity', 'users', 'database', 'monitoring', 'messages', 'server-console'];
  }
  if (role === 'principal') {
    return ['dashboard', 'reports', 'notices', 'departments', 'activity', 'users', 'database'];
  }
  if (role === 'hod') {
    return ['dashboard', 'reports', 'notices', 'activity', 'messages'];
  }
  if (role === 'deo') {
    return ['reports', 'notices', 'activity', 'users', 'messages'];
  }
  return ['recent-tests', 'notices', 'test-database', 'message-history'];
}

export function defaultTabForRole(role: Role) {
  if (role === 'admin') return 'dashboard';
  if (role === 'deo') return 'reports';
  if (role === 'principal' || role === 'hod') return 'dashboard';
  return 'recent-tests';
}

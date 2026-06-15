import type { AuthUser } from '../lib/roles.js';

declare module 'hono' {
  interface ContextVariableMap {
    authUser: AuthUser;
    realAuthUser: AuthUser;
    sessionId: string;
    sessionAuthUser: AuthUser;
    sessionEndNotice: {
      title: string;
      message: string;
      reason: string;
    } | null;
    archiveView: {
      active: boolean;
      archiveName: string;
      academicYear: string;
    } | null;
    testModeTarget: AuthUser;
  }
}

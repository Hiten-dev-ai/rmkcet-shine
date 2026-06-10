import type { AuthUser } from '../lib/roles.js';

declare module 'hono' {
  interface ContextVariableMap {
    authUser: AuthUser;
    realAuthUser: AuthUser;
    sessionId: string;
    sessionAuthUser: AuthUser;
    testModeTarget: AuthUser;
  }
}

import { useEffect, useMemo, useState } from 'react';
import type { MonitoringOverviewPayload, SessionHistoryRecord, SessionMonitoringRecord } from '../types';

const SESSION_PAGE_SIZE = 40;
const HISTORY_PAGE_SIZE = 50;

type MonitoringTabProps = {
  currentUserEmail: string;
  monitoringData: MonitoringOverviewPayload | null;
  monitoringLoading: boolean;
  monitoringSearch: string;
  monitoringStatusFilter: string;
  monitoringAuthFilter: string;
  monitoringDateFilter: string;
  filteredMonitoringSessions: SessionMonitoringRecord[];
  filteredMonitoringHistory: SessionHistoryRecord[];
  onMonitoringSearchChange: (value: string) => void;
  onMonitoringStatusFilterChange: (value: string) => void;
  onMonitoringAuthFilterChange: (value: string) => void;
  onMonitoringDateFilterChange: (value: string) => void;
  onMonitoringReset: () => void;
  onMonitoringRefresh: () => void;
  onLogoutAllUsers: () => void;
  onForceLogout: (email: string) => void;
  formatUtcSqlDateTime: (value: string | null | undefined) => string;
};

export default function MonitoringTab({
  currentUserEmail,
  monitoringData,
  monitoringLoading,
  monitoringSearch,
  monitoringStatusFilter,
  monitoringAuthFilter,
  monitoringDateFilter,
  filteredMonitoringSessions,
  filteredMonitoringHistory,
  onMonitoringSearchChange,
  onMonitoringStatusFilterChange,
  onMonitoringAuthFilterChange,
  onMonitoringDateFilterChange,
  onMonitoringReset,
  onMonitoringRefresh,
  onLogoutAllUsers,
  onForceLogout,
  formatUtcSqlDateTime,
}: MonitoringTabProps) {
  const [visibleSessionCount, setVisibleSessionCount] = useState(SESSION_PAGE_SIZE);
  const [visibleHistoryCount, setVisibleHistoryCount] = useState(HISTORY_PAGE_SIZE);

  useEffect(() => {
    setVisibleSessionCount(SESSION_PAGE_SIZE);
    setVisibleHistoryCount(HISTORY_PAGE_SIZE);
  }, [
    filteredMonitoringHistory.length,
    filteredMonitoringSessions.length,
    monitoringAuthFilter,
    monitoringDateFilter,
    monitoringSearch,
    monitoringStatusFilter,
  ]);

  const visibleMonitoringSessions = useMemo(
    () => filteredMonitoringSessions.slice(0, visibleSessionCount),
    [filteredMonitoringSessions, visibleSessionCount],
  );
  const visibleMonitoringHistory = useMemo(
    () => filteredMonitoringHistory.slice(0, visibleHistoryCount),
    [filteredMonitoringHistory, visibleHistoryCount],
  );
  const normalizedCurrentUserEmail = String(currentUserEmail || '').trim().toLowerCase();

  return (
    <>
      {!monitoringData?.sessionLog.ok ? (
        <div className="card mb-3" style={{ border: '1px solid rgba(245,158,11,.45)' }}>
          <div className="card-title"><i className="fas fa-triangle-exclamation"></i> Under Maintenance</div>
          <p style={{ fontSize: '.88rem', color: 'var(--text-dim)' }}>{monitoringData?.sessionLog.message || 'Session monitoring is temporarily unavailable.'}</p>
        </div>
      ) : null}

      <div className="metrics-grid mb-3">
        <div className="metric-card">
          <div className="metric-label">Active Sessions</div>
          <div className="metric-value">{monitoringData?.stats.active_sessions ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-signal"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Peak Concurrent</div>
          <div className="metric-value">{monitoringData?.stats.peak_concurrent ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-chart-line"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Forced Logouts</div>
          <div className="metric-value">{monitoringData?.stats.forced_logouts ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-power-off"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Avg Duration (min)</div>
          <div className="metric-value">{monitoringData?.stats.avg_duration_minutes ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-hourglass-half"></i></div>
        </div>
      </div>

      <div className="card mb-3">
        <div className="global-action-bar">
          <div className="form-group" style={{ flex: 1, minWidth: 280 }}>
            <label className="form-label">Search Sessions</label>
            <input
              className="form-control"
              value={monitoringSearch}
              onChange={(event) => onMonitoringSearchChange(event.target.value)}
              placeholder="Type user, email, department, IP or logout reason"
            />
          </div>
          <div className="form-group" style={{ minWidth: 170 }}>
            <label className="form-label">Status</label>
            <select className="form-control" value={monitoringStatusFilter} onChange={(event) => onMonitoringStatusFilterChange(event.target.value)}>
              <option value="all">All Statuses</option>
              <option value="active">Active</option>
              <option value="idle">Idle</option>
              <option value="inactive">Inactive</option>
              <option value="unknown">Unknown</option>
            </select>
          </div>
          <div className="form-group" style={{ minWidth: 170 }}>
            <label className="form-label">Method</label>
            <select className="form-control" value={monitoringAuthFilter} onChange={(event) => onMonitoringAuthFilterChange(event.target.value)}>
              <option value="all">All Methods</option>
              <option value="password">Password</option>
              <option value="password_failed">Password Failed</option>
              <option value="google">Google</option>
              <option value="google_failed">Google Failed</option>
            </select>
          </div>
          <div className="form-group" style={{ minWidth: 180 }}>
            <label className="form-label">Session Date</label>
            <input
              className="form-control"
              type="date"
              value={monitoringDateFilter}
              onChange={(event) => onMonitoringDateFilterChange(event.target.value)}
            />
          </div>
          <div className="form-group" style={{ minWidth: 120, alignSelf: 'end' }}>
            <button type="button" className="btn btn-outline btn-sm" onClick={onMonitoringReset}>
              <i className="fas fa-rotate-left"></i> Reset
            </button>
          </div>
        </div>
      </div>

      <div className="card mb-3">
        <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
          <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-desktop"></i> Active Sessions ({filteredMonitoringSessions.length})</div>
          <div className="btn-group">
            <button type="button" className="btn btn-outline btn-sm" onClick={onMonitoringRefresh} disabled={monitoringLoading}>
              <i className={`fas fa-rotate ${monitoringLoading ? 'fa-spin' : ''}`}></i> Refresh
            </button>
            <button type="button" className="btn btn-danger btn-sm" onClick={onLogoutAllUsers}>
              <i className="fas fa-power-off"></i> Logout Others
            </button>
          </div>
        </div>
        <div className="table-wrapper table-scroll-lg">
          <table className="sticky-table">
            <thead>
              <tr>
                <th>User</th>
                <th>Role</th>
                <th>Auth</th>
                <th>Dept</th>
                <th>Status</th>
                <th>Last Activity</th>
                <th>Actions</th>
              </tr>
            </thead>
            <tbody>
              {monitoringLoading && !monitoringData ? (
                <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading sessions...</td></tr>
              ) : filteredMonitoringSessions.length ? visibleMonitoringSessions.map((session) => {
                const sessionEmail = String(session.user_email || '').trim().toLowerCase();
                const isCurrentUser = Boolean(sessionEmail && sessionEmail === normalizedCurrentUserEmail);
                return (
                <tr key={session.session_id}>
                  <td><strong>{session.name || session.login_email || session.user_email}</strong><br /><span className="inline-muted">{session.login_email || session.user_email}</span></td>
                  <td><span className="badge badge-primary">{session.role || 'N/A'}</span></td>
                  <td><span className={`badge ${String(session.auth_method || 'password').toLowerCase().startsWith('google') ? 'badge-info' : String(session.auth_method || 'password').toLowerCase() === 'password_failed' ? 'badge-danger' : 'badge-muted'}`}>{String(session.auth_method || 'password').toLowerCase() === 'google' ? 'Google' : String(session.auth_method || 'password').toLowerCase() === 'password_failed' ? 'Password Failed' : 'Password'}</span></td>
                  <td>{session.department || 'N/A'}</td>
                  <td><span className={`badge ${session.status === 'Active' ? 'badge-success' : session.status === 'Idle' ? 'badge-warning' : 'badge-muted'}`}>{session.status}</span></td>
                  <td style={{ fontSize: '.82rem' }}>
                    <div>{formatUtcSqlDateTime(session.last_user_activity || session.last_activity)}</div>
                    <div className="inline-muted">{session.time_ago || '--'}</div>
                  </td>
                  <td>
                    {isCurrentUser ? (
                      <span className="badge badge-muted">Current Session</span>
                    ) : (
                      <button type="button" className="btn btn-danger btn-sm" disabled={!sessionEmail} onClick={() => onForceLogout(session.user_email)}>
                        <i className="fas fa-sign-out-alt"></i> Kick
                      </button>
                    )}
                  </td>
                </tr>
                );
              }) : (
                <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No active sessions matched the current filters.</td></tr>
              )}
            </tbody>
          </table>
        </div>
        {filteredMonitoringSessions.length > SESSION_PAGE_SIZE ? (
          <div className="d-flex justify-between align-center flex-wrap mt-2" style={{ gap: 10 }}>
            <span className="inline-muted">Showing {Math.min(visibleSessionCount, filteredMonitoringSessions.length)} of {filteredMonitoringSessions.length} active sessions</span>
            {visibleSessionCount < filteredMonitoringSessions.length ? (
              <button type="button" className="btn btn-outline btn-sm" onClick={() => setVisibleSessionCount((count) => count + SESSION_PAGE_SIZE)}>
                <i className="fas fa-chevron-down"></i> Show More
              </button>
            ) : null}
          </div>
        ) : null}
      </div>

      <div className="card">
        <div className="card-title"><i className="fas fa-clock-rotate-left"></i> Session History ({filteredMonitoringHistory.length})</div>
        <div className="table-wrapper table-scroll-lg">
          <table className="sticky-table">
            <thead>
              <tr>
                <th>User</th>
                <th>Role</th>
                <th>Login</th>
                <th>Dept</th>
                <th>Login Time</th>
                <th>Last Activity</th>
                <th>Duration</th>
                <th>Logout Reason</th>
              </tr>
            </thead>
            <tbody>
              {filteredMonitoringHistory.length ? visibleMonitoringHistory.map((entry) => (
                <tr key={`${entry.session_id}:${entry.login_time}:${entry.last_activity}`}>
                  <td><strong>{entry.name || entry.login_email || entry.user_email}</strong><br /><span className="inline-muted">{entry.login_email || entry.user_email}</span></td>
                  <td>{entry.role || 'N/A'}</td>
                  <td>
                    <span className={`badge ${String(entry.auth_method || 'password').toLowerCase().startsWith('google') ? 'badge-info' : 'badge-muted'}`}>
                      {String(entry.auth_method || 'password').toLowerCase() === 'google_unregistered'
                        ? 'Google Failed'
                        : String(entry.auth_method || 'password').toLowerCase() === 'password_failed'
                          ? 'Password Failed'
                        : String(entry.auth_method || 'password').toLowerCase() === 'google'
                          ? 'Google'
                          : 'Password'}
                    </span>
                  </td>
                  <td>{entry.department || 'N/A'}</td>
                  <td>{formatUtcSqlDateTime(entry.login_time)}</td>
                  <td>{formatUtcSqlDateTime(entry.last_activity)}</td>
                  <td>{entry.duration || '--'}</td>
                  <td>{entry.logout_reason || '--'}</td>
                </tr>
              )) : (
                <tr><td colSpan={8} className="text-center text-muted" style={{ padding: 24 }}>No session history matched the current filters.</td></tr>
              )}
            </tbody>
          </table>
        </div>
        {filteredMonitoringHistory.length > HISTORY_PAGE_SIZE ? (
          <div className="d-flex justify-between align-center flex-wrap mt-2" style={{ gap: 10 }}>
            <span className="inline-muted">Showing {Math.min(visibleHistoryCount, filteredMonitoringHistory.length)} of {filteredMonitoringHistory.length} history rows</span>
            {visibleHistoryCount < filteredMonitoringHistory.length ? (
              <button type="button" className="btn btn-outline btn-sm" onClick={() => setVisibleHistoryCount((count) => count + HISTORY_PAGE_SIZE)}>
                <i className="fas fa-chevron-down"></i> Show More
              </button>
            ) : null}
          </div>
        ) : null}
      </div>
    </>
  );
}

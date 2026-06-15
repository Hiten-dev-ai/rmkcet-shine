import type { AuthUser, DashboardOverviewPayload } from '../types';

type DashboardTabProps = {
  currentUser: AuthUser;
  dashboardLoading: boolean;
  dashboardData: DashboardOverviewPayload | null;
  formatDateTime: (value: string | null | undefined) => string;
  formatYearLevel: (year: number) => string;
  onRefreshDashboard: () => void;
  onCopyActivityDefaulters: () => void;
  onCopyDashboardNoticeDefaulters: () => void;
};

export default function DashboardTab({
  currentUser,
  dashboardLoading,
  dashboardData,
  formatDateTime,
  formatYearLevel,
  onRefreshDashboard,
  onCopyActivityDefaulters,
  onCopyDashboardNoticeDefaulters,
}: DashboardTabProps) {
  if (dashboardLoading && !dashboardData) {
    return (
      <div className="card">
        <div className="panel-placeholder">Loading dashboard...</div>
      </div>
    );
  }

  return (
    <>
      <div className="d-flex justify-between align-center flex-wrap mb-3" style={{ gap: 12 }}>
        <h3 className="section-title" style={{ marginBottom: 0 }}>
          <i className="fas fa-gauge"></i> Dashboard
        </h3>
        <button type="button" className="btn btn-outline btn-sm" onClick={onRefreshDashboard}>
          <i className="fas fa-rotate"></i> Refresh
        </button>
      </div>

      {currentUser.role === 'admin' && dashboardData?.admin_status ? (
        <>
          <div className="metrics-grid mb-3">
            <div className="metric-card">
              <div className="metric-label">Active Sessions</div>
              <div className="metric-value">{dashboardData.admin_status.sessions.active_sessions}</div>
              <div className="metric-icon"><i className="fas fa-signal"></i></div>
            </div>
            <div className="metric-card">
              <div className="metric-label">Today Sessions</div>
              <div className="metric-value">{dashboardData.admin_status.sessions.today_sessions}</div>
              <div className="metric-icon"><i className="fas fa-calendar-day"></i></div>
            </div>
            <div className="metric-card">
              <div className="metric-label">Backups</div>
              <div className="metric-value">{dashboardData.admin_status.backup.backup_count + dashboardData.admin_status.backup.auto_backup_count}</div>
              <div className="metric-icon"><i className="fas fa-database"></i></div>
            </div>
            <div className="metric-card">
              <div className="metric-label">Archives</div>
              <div className="metric-value">{dashboardData.admin_status.backup.archive_count}</div>
              <div className="metric-icon"><i className="fas fa-box-archive"></i></div>
            </div>
          </div>

          <div className="dashboard-dual-grid mb-3">
            <div className="card dashboard-status-card">
              <div className="card-title"><i className="fas fa-envelope"></i> SMTP Status</div>
              <div className="dashboard-summary-row">
                <span className={`badge ${dashboardData.admin_status.smtp.state === 'ready' ? 'badge-success' : 'badge-warning'}`}>{dashboardData.admin_status.smtp.label}</span>
              </div>
              <p className="inline-muted" style={{ marginBottom: 10 }}>{dashboardData.admin_status.smtp.detail}</p>
              <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                <div><strong>Server:</strong> {dashboardData.admin_status.smtp.config.server || '--'}</div>
                <div><strong>Username:</strong> {dashboardData.admin_status.smtp.config.username || '--'}</div>
                <div><strong>From:</strong> {dashboardData.admin_status.smtp.config.email_from || '--'}</div>
                <div><strong>Port:</strong> {dashboardData.admin_status.smtp.config.port || '--'}</div>
              </div>
            </div>

            <div className="card dashboard-status-card">
              <div className="card-title"><i className="fas fa-hard-drive"></i> Backup Status</div>
              <div className="dashboard-summary-row">
                <span className={`badge ${dashboardData.admin_status.backup.health === 'healthy' ? 'badge-success' : dashboardData.admin_status.backup.health === 'warning' ? 'badge-warning' : 'badge-danger'}`}>{dashboardData.admin_status.backup.label}</span>
                <span className="badge badge-primary">{dashboardData.admin_status.backup.storage_mode === 'gdrive' ? 'Google Drive' : 'Local'}</span>
              </div>
              <p className="inline-muted" style={{ marginBottom: 10 }}>{dashboardData.admin_status.backup.detail}</p>
              <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                <div><strong>Auto Backups:</strong> {dashboardData.admin_status.backup.auto_backup_count}</div>
                <div><strong>Manual Backups:</strong> {dashboardData.admin_status.backup.backup_count}</div>
                <div><strong>Archives:</strong> {dashboardData.admin_status.backup.archive_count}</div>
                <div><strong>Periodic Backups:</strong> {dashboardData.admin_status.backup.periodic_enabled ? 'Enabled' : 'Disabled'}</div>
                <div><strong>Drive Configured:</strong> {dashboardData.admin_status.backup.drive_configured ? 'Yes' : 'No'}</div>
                <div><strong>Latest Backup:</strong> {dashboardData.admin_status.backup.latest_backup_name ? `${dashboardData.admin_status.backup.latest_backup_name} (${dashboardData.admin_status.backup.latest_backup_modified})` : '--'}</div>
              </div>
            </div>
          </div>

          <div className="dashboard-dual-grid mb-3">
            <div className="card dashboard-status-card">
              <div className="card-title"><i className="fab fa-google"></i> OAuth Status</div>
              <div className="dashboard-summary-row">
                <span className={`badge ${dashboardData.admin_status.oauth.enabled && dashboardData.admin_status.oauth.healthy ? 'badge-success' : dashboardData.admin_status.oauth.enabled ? 'badge-warning' : 'badge-muted'}`}>{dashboardData.admin_status.oauth.label}</span>
                <span className="badge badge-warning">Today Failed {dashboardData.admin_status.oauth.today_unregistered_attempts}</span>
              </div>
              <p className="inline-muted" style={{ marginBottom: 10 }}>{dashboardData.admin_status.oauth.detail}</p>
              <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                <div><strong>Allowed Domain:</strong> {dashboardData.admin_status.oauth.allowed_domain || 'Any verified email'}</div>
                <div><strong>Redirect Base URL:</strong> {dashboardData.admin_status.oauth.redirect_base_url || '--'}</div>
                <div><strong>Unregistered Attempts Today:</strong> {dashboardData.admin_status.oauth.today_unregistered_attempts}</div>
                <div><strong>Total Unregistered Attempts:</strong> {dashboardData.admin_status.oauth.total_unregistered_attempts}</div>
                <div><strong>Latest Failed Email:</strong> {dashboardData.admin_status.oauth.latest_unregistered_attempt_email || '--'}</div>
                <div><strong>Latest Failed Time:</strong> {dashboardData.admin_status.oauth.latest_unregistered_attempt_time ? formatDateTime(dashboardData.admin_status.oauth.latest_unregistered_attempt_time) : '--'}</div>
              </div>
            </div>

            <div className="card dashboard-status-card">
              <div className="card-title"><i className="fas fa-user-shield"></i> Session Health</div>
              <div className="dashboard-summary-row">
                <span className="badge badge-success">Peak {dashboardData.admin_status.sessions.peak_concurrent}</span>
                <span className="badge badge-warning">Forced {dashboardData.admin_status.sessions.forced_logouts}</span>
              </div>
              <div style={{ display: 'grid', gap: 8, fontSize: '.84rem' }}>
                <div><strong>Active Sessions:</strong> {dashboardData.admin_status.sessions.active_sessions}</div>
                <div><strong>Today Logins:</strong> {dashboardData.admin_status.sessions.today_sessions}</div>
                <div><strong>Peak Concurrent:</strong> {dashboardData.admin_status.sessions.peak_concurrent}</div>
                <div><strong>Forced Logouts:</strong> {dashboardData.admin_status.sessions.forced_logouts}</div>
              </div>
            </div>
          </div>
        </>
      ) : null}

      <div className="dashboard-dual-grid mb-3">
        <div className="card dashboard-status-card">
          <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
            <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-file-lines"></i> Counsellor Completion Status For Marks</div>
            {currentUser.role === 'hod' ? (
              <button type="button" className="btn btn-outline btn-sm" onClick={onCopyActivityDefaulters}>
                <i className="fas fa-copy"></i> Copy Defaulters
              </button>
            ) : null}
          </div>
          <div className="dashboard-summary-row">
            <span className="badge badge-warning">Pending {dashboardData?.completion_overview.pending_counselors ?? 0}</span>
            <span className="badge badge-success">Overall {dashboardData?.completion_overview.overall ?? 0}%</span>
          </div>
          <div className="table-wrapper">
            <table>
              <thead>
                <tr>
                  <th>Department</th>
                  <th>Completion %</th>
                  <th>Year Breakdown</th>
                </tr>
              </thead>
              <tbody>
                {(dashboardData?.completion_overview.department_labels || []).length ? dashboardData!.completion_overview.department_labels.map((department, index) => (
                  <tr key={department}>
                    <td><strong>{department}</strong></td>
                    <td>{dashboardData!.completion_overview.department_values[index] ?? 0}%</td>
                    <td style={{ fontSize: '.8rem', color: 'var(--text-dim)' }}>
                      {Object.entries(dashboardData!.completion_overview.department_year_breakdown[department] || {})
                        .map(([year, value]) => `${formatYearLevel(Number(year))}: ${value}%`)
                        .join(' | ') || '--'}
                    </td>
                  </tr>
                )) : (
                  <tr><td colSpan={3} className="text-center text-muted" style={{ padding: 20 }}>No counselor completion data available yet.</td></tr>
                )}
              </tbody>
            </table>
          </div>
        </div>

        <div className="card dashboard-status-card">
          <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
            <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-bullhorn"></i> Notice Completion Status</div>
            {currentUser.role === 'hod' ? (
              <button type="button" className="btn btn-outline btn-sm" onClick={onCopyDashboardNoticeDefaulters}>
                <i className="fas fa-copy"></i> Copy Defaulters
              </button>
            ) : null}
          </div>
          <div className="dashboard-summary-row">
            <span className="badge badge-warning">Pending {dashboardData?.notice_completion_overview.pending_counselors ?? 0}</span>
            <span className="badge badge-success">Overall {dashboardData?.notice_completion_overview.overall ?? 0}%</span>
          </div>
          <div className="table-wrapper">
            <table>
              <thead>
                <tr>
                  <th>Department</th>
                  <th>Completion %</th>
                  <th>Year Breakdown</th>
                </tr>
              </thead>
              <tbody>
                {(dashboardData?.notice_completion_overview.department_labels || []).length ? dashboardData!.notice_completion_overview.department_labels.map((department, index) => (
                  <tr key={`notice-${department}`}>
                    <td><strong>{department}</strong></td>
                    <td>{dashboardData!.notice_completion_overview.department_values[index] ?? 0}%</td>
                    <td style={{ fontSize: '.8rem', color: 'var(--text-dim)' }}>
                      {Object.entries(dashboardData!.notice_completion_overview.department_year_breakdown[department] || {})
                        .map(([year, value]) => `${formatYearLevel(Number(year))}: ${value}%`)
                        .join(' | ') || '--'}
                    </td>
                  </tr>
                )) : (
                  <tr><td colSpan={3} className="text-center text-muted" style={{ padding: 20 }}>No notice completion data available yet.</td></tr>
                )}
              </tbody>
            </table>
          </div>
        </div>
      </div>

      <div className="card">
        <div className="card-title"><i className="fas fa-trophy"></i> Top Counselors (Completion)</div>
        <div className="table-wrapper">
          <table>
            <thead>
              <tr>
                <th>Name</th>
                <th>Department</th>
                <th>Students</th>
                <th>Reached</th>
                <th>Completion</th>
              </tr>
            </thead>
            <tbody>
              {(dashboardData?.leaderboard || []).length ? dashboardData!.leaderboard.map((row) => (
                <tr key={row.email}>
                  <td><strong>{row.name}</strong><br /><span className="inline-muted">{row.email}</span></td>
                  <td>{row.department}</td>
                  <td>{row.student_count}</td>
                  <td>{row.unique_students_messaged}</td>
                  <td><span className="badge badge-success">{row.completion_pct}%</span></td>
                </tr>
              )) : (
                <tr><td colSpan={5} className="text-center text-muted" style={{ padding: 20 }}>No counselor activity yet.</td></tr>
              )}
            </tbody>
          </table>
        </div>
      </div>
    </>
  );
}

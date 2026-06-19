import { useCallback, useMemo } from 'react';
import type { ComponentType } from 'react';
import { VirtualizedRowsTable } from '../components/VirtualizedRowsTable';
import type { ActivityOverviewPayload, CounselorActivityRow, DepartmentRecord } from '../types';

type BreadcrumbProps = {
  icon: string;
  items: Array<{ label: string; onClick?: () => void }>;
};

type ActivityFiltersState = {
  department: string;
  year: string;
  semester: string;
  test_name: string;
  q: string;
  sort: string;
};

type ActivityCopyMode = 'scope' | 'department' | 'year' | 'test';

type ActivityTabProps = {
  activityLoading: boolean;
  activityCopying: boolean;
  activityPdfLoading: boolean;
  activityData: ActivityOverviewPayload | null;
  activityDisplayRows: CounselorActivityRow[];
  activityFilters: ActivityFiltersState;
  ScopeBreadcrumb: ComponentType<BreadcrumbProps>;
  formatYearLevel: (year: number) => string;
  formatDateTime: (value: string | null | undefined) => string;
  onLoadActivityOverview: (filters?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
    q?: string;
    sort?: string;
  }) => void;
  onActivitySearchChange: (value: string) => void;
  onActivitySortChange: (value: string) => void;
  onResetActivityToRoot: () => void;
  onCopyActivityDefaulters: (mode: ActivityCopyMode, options?: {
    department?: string;
    year?: number | null;
    semester?: string;
    test_name?: string;
  }) => void;
  onDownloadActivityScopePdf: () => void;
};

export default function ActivityTab({
  activityLoading,
  activityCopying,
  activityPdfLoading,
  activityData,
  activityDisplayRows,
  activityFilters,
  ScopeBreadcrumb,
  formatYearLevel,
  formatDateTime,
  onLoadActivityOverview,
  onActivitySearchChange,
  onActivitySortChange,
  onResetActivityToRoot,
  onCopyActivityDefaulters,
  onDownloadActivityScopePdf,
}: ActivityTabProps) {
  const activityColumns = useMemo(() => [
    {
      key: 'counselor',
      label: 'Counselor',
      width: '2.4fr',
      className: 'virtualized-table-cell-stack',
      render: (row: CounselorActivityRow) => (
        <div className="virtualized-counselor-cell">
          <strong>{row.name}</strong>
          <span className="inline-muted virtualized-email-text">{row.email}</span>
        </div>
      ),
    },
    { key: 'department', label: 'Department', width: '0.9fr', render: (row: CounselorActivityRow) => row.department },
    {
      key: 'status',
      label: 'Status',
      width: '0.95fr',
      render: (row: CounselorActivityRow) => <span className={`badge ${row.work_status === 'Complete' ? 'badge-success' : 'badge-warning'}`}>{row.work_status}</span>,
    },
    { key: 'completion', label: 'Completion %', width: '0.95fr', render: (row: CounselorActivityRow) => `${row.completion_pct}%` },
    { key: 'year', label: 'Year', width: '0.9fr', render: (row: CounselorActivityRow) => formatYearLevel(row.year_level || 1) },
    { key: 'students', label: 'Students', width: '0.75fr', render: (row: CounselorActivityRow) => row.student_count },
    { key: 'reached', label: 'Reached', width: '0.75fr', render: (row: CounselorActivityRow) => row.unique_students_messaged },
    { key: 'pending', label: 'Pending', width: '0.75fr', render: (row: CounselorActivityRow) => row.pending_count },
    {
      key: 'lastLogin',
      label: 'Last Login',
      width: '1.2fr',
      className: 'virtualized-table-cell-muted',
      render: (row: CounselorActivityRow) => formatDateTime(row.last_login || 'Never'),
    },
  ], [formatDateTime, formatYearLevel]);
  const activityRowKey = useCallback((row: CounselorActivityRow) => row.email, []);

  if (activityLoading && !activityData) {
    return (
      <div className="card">
        <div className="panel-placeholder">Loading counselor activity...</div>
      </div>
    );
  }

  return (
    <div data-tour-id="activity-workspace">
      {activityData?.showDepartmentPicker ? (
        <div className="mb-3">
          <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 10 }}>
            <h3 className="section-title" style={{ margin: 0 }}><i className="fas fa-building"></i> Select Department</h3>
            <div className="btn-group">
              <button type="button" className="btn btn-outline btn-sm" onClick={() => onCopyActivityDefaulters('scope')}>
                <i className={`fas ${activityCopying ? 'fa-spinner fa-spin' : 'fa-copy'}`}></i> {activityCopying ? 'Preparing...' : 'Copy Defaulters'}
              </button>
              <button type="button" className="btn btn-outline btn-sm" onClick={onDownloadActivityScopePdf} disabled={activityPdfLoading}>
                <i className={`fas ${activityPdfLoading ? 'fa-spinner fa-spin' : 'fa-file-pdf'}`}></i> {activityPdfLoading ? 'Preparing PDF...' : 'Full Scope PDF'}
              </button>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => onLoadActivityOverview()}>
                <i className="fas fa-rotate"></i> Refresh
              </button>
            </div>
          </div>
          <div className="metrics-grid selection-grid department-selection-grid">
            {(activityData?.departments || []).map((department: DepartmentRecord) => (
              <button
                key={department.code}
                type="button"
                className="metric-card selection-card-button"
                onClick={() => onLoadActivityOverview({ department: department.code })}
              >
                <div className="metric-value" style={{ fontSize: '1.6rem' }}>{department.code}</div>
                <div className="selection-card-subtitle">{department.name}</div>
              </button>
            ))}
          </div>
        </div>
      ) : null}

      {activityData?.showYearPicker ? (
        <div className="selection-shell selection-shell-stage-enter mb-3" style={{ maxWidth: 620 }}>
          <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
            <ScopeBreadcrumb
              icon="fa-layer-group"
              items={[
                { label: 'Counsellor Activity', onClick: onResetActivityToRoot },
                { label: activityData.selectedDepartment || 'Department' },
              ]}
            />
            <button
              type="button"
              className="btn btn-outline btn-sm"
              onClick={() => onCopyActivityDefaulters('department', { department: activityData.selectedDepartment })}
              disabled={activityCopying}
            >
              <i className={`fas ${activityCopying ? 'fa-spinner fa-spin' : 'fa-copy'}`}></i> {activityCopying ? 'Preparing...' : 'Copy Defaulters'}
            </button>
          </div>
          <div className="selection-actions-grid">
            {(activityData.availableYears || []).map((year) => (
              <button
                key={year}
                type="button"
                className="btn btn-outline selection-action-button"
                onClick={() => onLoadActivityOverview({ department: activityData.selectedDepartment, year })}
              >
                {formatYearLevel(year)}
              </button>
            ))}
          </div>
        </div>
      ) : null}

      {activityData && !activityData.showDepartmentPicker && !activityData.showYearPicker ? (
        <div className="card mb-3">
          <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
            <ScopeBreadcrumb
              icon="fa-layer-group"
              items={[
                { label: 'Counsellor Activity', onClick: () => onLoadActivityOverview() },
                { label: activityData.selectedDepartment, onClick: () => onLoadActivityOverview({ department: activityData.selectedDepartment }) },
                { label: formatYearLevel(activityData.selectedYear || 1) },
              ]}
            />
            <div className="btn-group">
              <button
                type="button"
                className="btn btn-outline btn-sm"
                onClick={() => onCopyActivityDefaulters('year', {
                  department: activityData.selectedDepartment,
                  year: activityData.selectedYear,
                })}
                disabled={activityCopying}
              >
                <i className={`fas ${activityCopying ? 'fa-spinner fa-spin' : 'fa-copy'}`}></i> {activityCopying ? 'Preparing...' : 'Copy Defaulters'}
              </button>
            </div>
          </div>
          <div className="test-status-grid">
            {['1', '2'].map((semester) => (
              <div key={semester} className="card test-status-panel">
                <div className="d-flex justify-between align-center" style={{ gap: 10, marginBottom: 12 }}>
                  <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-layer-group"></i> Semester {semester}</div>
                </div>
                {['IAT 1', 'IAT 2', 'MODEL EXAM'].map((testName) => {
                  const uploaded = !!activityData.testStatus?.[semester]?.[testName];
                  const active = activityData.selectedSemester === semester && activityData.selectedTestName === testName;
                  return (
                    <div key={`${semester}:${testName}`} className="test-status-row">
                      <button
                        type="button"
                        className={`btn ${active ? 'btn-primary' : 'btn-outline'} test-status-button`}
                        onClick={() => onLoadActivityOverview({
                          department: activityData.selectedDepartment,
                          year: activityData.selectedYear,
                          semester,
                          test_name: testName,
                        })}
                      >
                        {testName}
                      </button>
                      <span className={`badge ${uploaded ? 'badge-success' : 'badge-warning'}`}>{uploaded ? 'Uploaded' : 'Upload Pending'}</span>
                    </div>
                  );
                })}
              </div>
            ))}
          </div>
        </div>
      ) : null}

      {activityData?.result ? (
        <>
          <div className="metrics-grid mb-3">
            <div className="metric-card">
              <div className="metric-label">Total Counselors</div>
              <div className="metric-value">{activityData.result.stats.total_counselors}</div>
              <div className="metric-icon"><i className="fas fa-users"></i></div>
            </div>
            <div className="metric-card">
              <div className="metric-label">Complete</div>
              <div className="metric-value">{activityData.result.stats.complete}</div>
              <div className="metric-icon"><i className="fas fa-circle-check"></i></div>
            </div>
            <div className="metric-card">
              <div className="metric-label">Pending</div>
              <div className="metric-value">{activityData.result.stats.pending}</div>
              <div className="metric-icon"><i className="fas fa-clock"></i></div>
            </div>
            <div className="metric-card">
              <div className="metric-label">Avg Completion</div>
              <div className="metric-value">{activityData.result.stats.avg_completion}%</div>
              <div className="metric-icon"><i className="fas fa-chart-line"></i></div>
            </div>
          </div>

          <div className="card mb-3">
            <div className="d-flex align-center flex-wrap" style={{ gap: 8 }}>
              <input
                className="form-control"
                style={{ maxWidth: 280, height: 34, padding: '6px 10px', fontSize: '.82rem' }}
                value={activityFilters.q}
                onChange={(event) => onActivitySearchChange(event.target.value)}
                placeholder="Search counselor"
              />
              <select className="form-control" style={{ maxWidth: 150, height: 34, padding: '6px 10px', fontSize: '.8rem' }} value={activityFilters.sort} onChange={(event) => onActivitySortChange(event.target.value)}>
                <option value="pending_first">Pending</option>
                <option value="name_asc">A-Z</option>
                <option value="name_desc">Z-A</option>
              </select>
              <button type="button" className="btn btn-outline btn-sm" style={{ height: 34 }} onClick={() => onLoadActivityOverview({
                department: activityData.selectedDepartment,
                year: activityData.selectedYear,
                semester: activityData.selectedSemester,
                test_name: activityData.selectedTestName,
              })}>
                <i className="fas fa-rotate"></i> Refresh
              </button>
              <button
                type="button"
                className="btn btn-outline btn-sm"
                style={{ height: 34 }}
                onClick={() => onCopyActivityDefaulters('test', {
                  department: activityData.selectedDepartment,
                  year: activityData.selectedYear,
                  semester: activityData.selectedSemester,
                  test_name: activityData.selectedTestName,
                })}
                disabled={activityCopying}
              >
                <i className={`fas ${activityCopying ? 'fa-spinner fa-spin' : 'fa-copy'}`}></i> {activityCopying ? 'Preparing...' : 'Copy Defaulters'}
              </button>
            </div>
          </div>

          <VirtualizedRowsTable
            columns={activityColumns}
            rows={activityDisplayRows}
            rowKey={activityRowKey}
            rowHeight={72}
            maxHeight={640}
            emptyMessage="No counselor rows found for the current search and sort filters."
          />
        </>
      ) : null}
    </div>
  );
}

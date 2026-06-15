import { useEffect, useMemo, useState } from 'react';
import type { ComponentType } from 'react';
import type { CdpOverviewPayload } from '../types';

type BreadcrumbProps = {
  icon: string;
  items: Array<{ label: string; onClick?: () => void }>;
};

type CdpFilters = {
  department?: string;
  year?: number | null;
  semester?: string;
  subject_id?: number | null;
};

type CdpTabProps = {
  cdpLoading: boolean;
  cdpData: CdpOverviewPayload | null;
  ScopeBreadcrumb: ComponentType<BreadcrumbProps>;
  formatYearLevel: (year: number) => string;
  formatDateTime: (value: string | null | undefined) => string;
  getSemesterLabel: (semester: string) => string;
  onLoadCdpOverview: (filters?: CdpFilters) => void;
  onRebuildScope: (filters: { department: string; year: number; semester: string; subject_id?: number | null }) => void;
  onShowCopyDialog: (title: string, message: string) => void;
  onShowNoDefaultersNotice: (message: string) => void;
  copyTemplate: string;
};

function getStatusBadge(status: 'ready' | 'pending' | 'error' | 'unparsed') {
  if (status === 'ready') return { className: 'badge-success', label: 'Complete' };
  if (status === 'pending') return { className: 'badge-warning', label: 'Pending' };
  if (status === 'error') return { className: 'badge-danger', label: 'Sheet Error' };
  return { className: 'badge-muted', label: 'Not Parsed' };
}

const MARK_ENTRY_TEST_ORDER = ['iat1', 'iat2', 'model', 'unit_test'] as const;

function getMarkEntryStatusBadge(status: 'complete' | 'pending' | 'not_available' | 'error') {
  if (status === 'complete') return { className: 'badge-success', label: 'Complete' };
  if (status === 'pending') return { className: 'badge-warning', label: 'Pending' };
  if (status === 'error') return { className: 'badge-danger', label: 'Error' };
  return { className: 'badge-muted', label: 'Not Available' };
}

function parsePendingDateLabelToTimestamp(
  value: string,
  subject?: { academic_start_year?: number | null; academic_end_year?: number | null } | null,
) {
  const match = String(value || '').trim().match(/^(\d{1,2})\/(\d{1,2})$/);
  if (!match) return null;
  const day = Number(match[1]);
  const month = Number(match[2]);
  if (!day || !month || day > 31 || month > 12) return null;
  const nowYear = new Date().getFullYear();
  const startYear = Number(subject?.academic_start_year || 0) || nowYear;
  const endYear = Number(subject?.academic_end_year || 0) || startYear;
  const year = month >= 6 ? startYear : endYear;
  return new Date(year, month - 1, day).getTime();
}

function fallbackCopy(text: string) {
  const textarea = document.createElement('textarea');
  textarea.value = text;
  textarea.setAttribute('readonly', 'true');
  textarea.style.position = 'fixed';
  textarea.style.opacity = '0';
  document.body.appendChild(textarea);
  textarea.select();
  document.execCommand('copy');
  document.body.removeChild(textarea);
}

async function copyText(text: string) {
  if (navigator.clipboard?.writeText) {
    await navigator.clipboard.writeText(text);
    return;
  }
  fallbackCopy(text);
}

function renderCopyTemplate(template: string, values: Record<string, string>) {
  return String(template || '').replace(/\{([a-zA-Z0-9_]+)\}/g, (_, key) => values[key] ?? '');
}

function buildFacultyPendingSummary(faculty: {
  pending_dates: string[];
  notes: string[];
  class_breakdown: Array<{ class_label: string; pending_dates: string[] }>;
}) {
  const classSummaries = (faculty.class_breakdown || [])
    .filter((item) => item.pending_dates.length)
    .map((item) => `${item.class_label}: ${item.pending_dates.join(', ')}`);
  if (classSummaries.length) return classSummaries.join(' | ');
  if (faculty.pending_dates.length) return faculty.pending_dates.join(', ');
  if (faculty.notes.length) return faculty.notes.join(' | ');
  return '';
}

function buildSubjectScopeLabel(subject: {
  department: string;
  year_level: number;
  semester: string;
}) {
  const yearSuffix = subject.year_level === 1 ? 'st' : subject.year_level === 2 ? 'nd' : subject.year_level === 3 ? 'rd' : 'th';
  const semesterLabel = String(subject.semester || '').trim() === '2' ? 'Sem - II' : 'Sem - I';
  return `${subject.department} / ${subject.year_level}${yearSuffix} Year / ${semesterLabel}`;
}

function buildSubjectPendingBlock(subject: {
  subject_code: string;
  subject_name: string;
  department: string;
  year_level: number;
  semester: string;
  parser_error?: string | null;
  faculty_statuses?: Array<{
    faculty_name: string;
    status: string;
    pending_dates: string[];
    notes: string[];
    class_breakdown: Array<{ class_label: string; pending_dates: string[] }>;
  }>;
}) {
  const lines = [
    `${subject.subject_code} - ${subject.subject_name}`,
    buildSubjectScopeLabel(subject),
  ];
  if (String(subject.parser_error || '').trim()) {
    lines.push(`Sheet Error: ${subject.parser_error}`);
    return lines;
  }
  (subject.faculty_statuses || [])
    .filter((faculty) => faculty.status !== 'ready' || faculty.pending_dates.length || faculty.notes.length)
    .forEach((faculty) => {
      lines.push(`${faculty.faculty_name}: ${buildFacultyPendingSummary(faculty) || 'Pending status detected'}`);
    });
  return lines;
}

function buildScopeDefaultersCopy(cdpData: CdpOverviewPayload) {
  const lines: string[] = [];
  (cdpData.subjects || []).forEach((subject) => {
    const pendingFaculty = (subject.faculty_statuses || []).filter((faculty) => faculty.status !== 'ready' || faculty.pending_dates.length || faculty.notes.length);
    if (!pendingFaculty.length && !subject.parser_error) return;
    lines.push(...buildSubjectPendingBlock(subject));
    lines.push('');
  });
  return lines.join('\n').trim();
}

function buildSubjectDefaultersCopy(
  subject: NonNullable<CdpOverviewPayload['selectedSubject']>,
  detail: NonNullable<CdpOverviewPayload['selectedSubjectDetail']>,
) {
  return buildSubjectPendingBlock({
    subject_code: subject.subject_code,
    subject_name: subject.subject_name,
    department: subject.department,
    year_level: subject.year_level,
    semester: subject.semester,
    parser_error: detail.parser_error,
    faculty_statuses: detail.faculty_statuses,
  }).join('\n').trim();
}

export default function CdpTab({
  cdpLoading,
  cdpData,
  ScopeBreadcrumb,
  formatYearLevel,
  formatDateTime,
  getSemesterLabel,
  onLoadCdpOverview,
  onRebuildScope,
  onShowCopyDialog,
  onShowNoDefaultersNotice,
  copyTemplate,
}: CdpTabProps) {
  const selectedDetail = cdpData?.selectedSubjectDetail || null;
  const selectedSubject = cdpData?.selectedSubject || null;
  const selectedStatusBadge = getStatusBadge(selectedDetail?.summary_status || 'unparsed');
  const showingSubjectDetailPage = Boolean(selectedSubject && selectedDetail);
  const [facultyFilter, setFacultyFilter] = useState('__all__');
  const [facultyDateFrom, setFacultyDateFrom] = useState('');
  const [facultyDateTo, setFacultyDateTo] = useState('');
  const [facultyDateFromFocused, setFacultyDateFromFocused] = useState(false);
  const [facultyDateToFocused, setFacultyDateToFocused] = useState(false);

  useEffect(() => {
    setFacultyFilter('__all__');
    setFacultyDateFrom('');
    setFacultyDateTo('');
    setFacultyDateFromFocused(false);
    setFacultyDateToFocused(false);
  }, [selectedSubject?.id]);

  const facultyOptions = useMemo(() => {
    if (!selectedDetail) return [];
    return selectedDetail.faculty_statuses
      .map((faculty) => String(faculty.faculty_name || '').trim())
      .filter(Boolean);
  }, [selectedDetail]);
  const markEntrySummaries = selectedDetail?.mark_entry?.summaries || [];
  const markEntrySummaryMap = useMemo(
    () => new Map(markEntrySummaries.map((summary) => [summary.key, summary] as const)),
    [markEntrySummaries],
  );

  const filteredFacultyStatuses = useMemo(() => {
    if (!selectedDetail || !selectedSubject) return [];
    const fromTs = facultyDateFrom ? new Date(`${facultyDateFrom}T00:00:00`).getTime() : null;
    const toTs = facultyDateTo ? new Date(`${facultyDateTo}T23:59:59`).getTime() : null;

    const rows = [...selectedDetail.faculty_statuses].filter((faculty) => {
      const facultyName = String(faculty.faculty_name || '').trim();
      if (facultyFilter !== '__all__' && facultyName !== facultyFilter) return false;
      if (!fromTs && !toTs) return true;
      const timestamps = faculty.pending_dates
        .map((value) => parsePendingDateLabelToTimestamp(value, selectedSubject))
        .filter((value): value is number => value !== null);
      if (!timestamps.length) return false;
      return timestamps.some((timestamp) => (fromTs === null || timestamp >= fromTs) && (toTs === null || timestamp <= toTs));
    });
    return rows;
  }, [facultyDateFrom, facultyDateTo, facultyFilter, selectedDetail, selectedSubject]);
  const markEntrySection = selectedDetail ? (
    <div className="card mt-3">
      <div className="card-title"><i className="fas fa-pen-to-square"></i> Mark Entry</div>
      <div
        style={{
          display: 'grid',
          gridTemplateColumns: 'repeat(auto-fit, minmax(180px, 1fr))',
          gap: 12,
          marginBottom: 16,
        }}
      >
        {markEntrySummaries.map((summary) => {
          const badge = getMarkEntryStatusBadge(summary.status);
          return (
            <div
              key={summary.key}
              style={{
                border: '1px solid var(--border)',
                borderRadius: 16,
                padding: '12px 14px',
                background: 'var(--panel-elevated)',
              }}
            >
              <div className="d-flex justify-between align-center" style={{ gap: 10, marginBottom: 10 }}>
                <strong style={{ fontSize: '.96rem' }}>{summary.label}</strong>
                <span className={`badge ${badge.className}`}>{badge.label}</span>
              </div>
              <div className="inline-muted" style={{ fontSize: '.84rem' }}>
                {summary.filled_students} / {summary.total_students} students
              </div>
              <div style={{ fontSize: '.9rem', fontWeight: 700, marginTop: 4 }}>
                {summary.completion_pct}% complete
              </div>
              {summary.message ? (
                <div className="inline-muted" style={{ fontSize: '.8rem', marginTop: 6 }}>
                  {summary.message}
                </div>
              ) : null}
            </div>
          );
        })}
      </div>
      {selectedDetail.mark_entry.rows.length ? (
        <div className="table-wrapper table-scroll-lg">
          <table className="sticky-table">
            <thead>
              <tr>
                <th>Faculty</th>
                <th>Class</th>
                <th>IAT I</th>
                <th>IAT II</th>
                <th>Model</th>
                <th>Unit Test</th>
              </tr>
            </thead>
            <tbody>
              {selectedDetail.mark_entry.rows.map((row) => (
                <tr key={`${row.faculty_name}:${row.class_label}`}>
                  <td><strong>{row.faculty_name}</strong></td>
                  <td><strong>{row.class_label}</strong></td>
                  {MARK_ENTRY_TEST_ORDER.map((testKey) => {
                    const cell = row.tests[testKey];
                    const badge = getMarkEntryStatusBadge(cell.status);
                    const summary = markEntrySummaryMap.get(testKey);
                    return (
                      <td key={`${row.faculty_name}:${row.class_label}:${testKey}`}>
                        <div style={{ display: 'grid', gap: 6 }}>
                          <div>
                            <span className={`badge ${badge.className}`}>{badge.label}</span>
                          </div>
                          <div style={{ fontSize: '.84rem', fontWeight: 700 }}>
                            {cell.completion_pct}% complete
                          </div>
                          <div className="inline-muted" style={{ fontSize: '.8rem' }}>
                            {cell.filled_students} / {cell.total_students} students
                          </div>
                          {cell.message ? (
                            <div className="inline-muted" style={{ fontSize: '.78rem' }}>
                              {cell.message}
                            </div>
                          ) : summary?.status === 'not_available' ? (
                            <div className="inline-muted" style={{ fontSize: '.78rem' }}>
                              {summary.message}
                            </div>
                          ) : null}
                        </div>
                      </td>
                    );
                  })}
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      ) : (
        <div className="inline-muted">
          Mark Entry rows will appear once faculty-class allocations are available for this subject.
        </div>
      )}
    </div>
  ) : null;

  async function handleCopyScopeDefaulters() {
    if (!cdpData) return;
    try {
      const pendingCount = (cdpData.subjects || []).reduce(
        (sum, subject) => sum + (subject.faculty_statuses || []).filter((faculty) => faculty.status !== 'ready' || faculty.pending_dates.length || faculty.notes.length).length,
        0,
      );
      const hasSheetErrors = (cdpData.subjects || []).some((subject) => Boolean(String(subject.parser_error || '').trim()));
      if (!pendingCount && !hasSheetErrors) {
        onShowNoDefaultersNotice('No defaulters were found for the selected CDP scope.');
        return;
      }
      const copiedText = renderCopyTemplate(copyTemplate, {
        count: String(pendingCount),
        scope: `${cdpData.selectedDepartment} / ${formatYearLevel(cdpData.selectedYear || 1)} / ${getSemesterLabel(cdpData.selectedSemester || '1')}`,
        entries: buildScopeDefaultersCopy(cdpData),
      });
      await copyText(copiedText);
      onShowCopyDialog(
        'Copied',
        `Copied ${pendingCount} pending faculty entr${pendingCount === 1 ? 'y' : 'ies'} from ${cdpData.selectedDepartment} / ${formatYearLevel(cdpData.selectedYear || 1)} / ${getSemesterLabel(cdpData.selectedSemester || '1')}.`,
      );
    } catch {
      onShowCopyDialog('Copy Failed', 'Unable to copy CDP defaulters right now.');
    }
  }

  async function handleCopySubjectDefaulters() {
    if (!selectedSubject || !selectedDetail) return;
    try {
      const pendingCount = (selectedDetail.faculty_statuses || []).filter((faculty) => faculty.status !== 'ready' || faculty.pending_dates.length || faculty.notes.length).length;
      const hasSheetError = Boolean(String(selectedDetail.parser_error || '').trim());
      if (!pendingCount && !hasSheetError) {
        onShowNoDefaultersNotice(`No defaulters were found for ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`);
        return;
      }
      const copiedText = renderCopyTemplate(copyTemplate, {
        count: String(pendingCount),
        scope: buildSubjectScopeLabel(selectedSubject),
        entries: buildSubjectDefaultersCopy(selectedSubject, selectedDetail),
      });
      await copyText(copiedText);
      onShowCopyDialog(
        'Copied',
        `Copied ${pendingCount} pending faculty entr${pendingCount === 1 ? 'y' : 'ies'} from ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`,
      );
    } catch {
      onShowCopyDialog('Copy Failed', 'Unable to copy CDP defaulters right now.');
    }
  }

  if (cdpLoading && !cdpData) {
    return (
      <div className="card">
        <div className="panel-placeholder">Rebuilding CDP scope...</div>
      </div>
    );
  }

  return (
    <>
      {cdpData?.showDepartmentPicker ? (
        <div className="mb-3">
          <h3 className="section-title" style={{ marginBottom: 14 }}><i className="fas fa-building"></i> Select Department</h3>
          <div className="metrics-grid selection-grid department-selection-grid">
            {(cdpData.departments || []).map((department) => (
              <button
                key={department.code}
                type="button"
                className="metric-card selection-card-button"
                onClick={() => onLoadCdpOverview({ department: department.code })}
              >
                <div className="metric-value" style={{ fontSize: '1.6rem' }}>{department.code}</div>
                <div className="selection-card-subtitle">{department.name}</div>
              </button>
            ))}
          </div>
        </div>
      ) : null}

      {cdpData?.showYearPicker ? (
        <div className="selection-shell selection-shell-stage-enter mb-3" style={{ maxWidth: 620 }}>
          <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
            <ScopeBreadcrumb
              icon="fa-clipboard-list"
              items={[
                { label: 'CDP', onClick: () => onLoadCdpOverview() },
                { label: cdpData.selectedDepartment || 'Department' },
              ]}
            />
          </div>
          <div className="selection-actions-grid">
            {(cdpData.availableYears || []).map((year) => (
              <button
                key={year}
                type="button"
                className="btn btn-outline selection-action-button"
                onClick={() => onLoadCdpOverview({ department: cdpData.selectedDepartment, year })}
              >
                {formatYearLevel(year)}
              </button>
            ))}
          </div>
        </div>
      ) : null}

      {cdpData?.showSemesterPicker ? (
        <div className="selection-shell selection-shell-stage-enter mb-3" style={{ maxWidth: 620 }}>
          <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
            <ScopeBreadcrumb
              icon="fa-clipboard-list"
              items={[
                { label: 'CDP', onClick: () => onLoadCdpOverview() },
                { label: cdpData.selectedDepartment, onClick: () => onLoadCdpOverview({ department: cdpData.selectedDepartment }) },
                { label: formatYearLevel(cdpData.selectedYear || 1) },
              ]}
            />
          </div>
          <div className="selection-actions-grid">
            {(cdpData.availableSemesters || []).map((semester) => (
              <button
                key={semester}
                type="button"
                className="btn btn-outline selection-action-button"
                onClick={() => onRebuildScope({
                  department: cdpData.selectedDepartment,
                  year: cdpData.selectedYear || 1,
                  semester,
                })}
              >
                {getSemesterLabel(semester)}
              </button>
            ))}
          </div>
        </div>
      ) : null}

      {cdpData && !cdpData.showDepartmentPicker && !cdpData.showYearPicker && !cdpData.showSemesterPicker ? (
        <>
          <div className="selection-shell mb-3">
            <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12 }}>
              <ScopeBreadcrumb
                icon="fa-clipboard-list"
                items={[
                  { label: 'CDP', onClick: () => onLoadCdpOverview() },
                  { label: cdpData.selectedDepartment, onClick: () => onLoadCdpOverview({ department: cdpData.selectedDepartment }) },
                  { label: formatYearLevel(cdpData.selectedYear || 1), onClick: () => onLoadCdpOverview({ department: cdpData.selectedDepartment, year: cdpData.selectedYear }) },
                  {
                    label: getSemesterLabel(cdpData.selectedSemester || '1'),
                    onClick: () => onLoadCdpOverview({
                      department: cdpData.selectedDepartment,
                      year: cdpData.selectedYear,
                      semester: cdpData.selectedSemester,
                    }),
                  },
                  ...(selectedSubject ? [{ label: selectedSubject.subject_code }] : []),
                ]}
              />
              <div className="btn-group">
                {!showingSubjectDetailPage ? (
                  <button
                    type="button"
                    className="btn btn-outline btn-sm"
                    onClick={() => void handleCopyScopeDefaulters()}
                  >
                    <i className="fas fa-copy"></i> Copy Defaulters
                  </button>
                ) : null}
                {showingSubjectDetailPage && selectedSubject?.google_sheet_link ? (
                  <a
                    href={selectedSubject.google_sheet_link}
                    target="_blank"
                    rel="noreferrer"
                    className="btn btn-outline btn-sm"
                  >
                    <i className="fas fa-link"></i> Open Sheet
                  </a>
                ) : null}
                <button
                  type="button"
                  className="btn btn-outline btn-sm"
                  disabled={cdpLoading}
                  onClick={() => onRebuildScope({
                    department: cdpData.selectedDepartment,
                    year: cdpData.selectedYear || 1,
                    semester: cdpData.selectedSemester,
                    subject_id: selectedSubject?.id || null,
                  })}
                >
                  <i className={`fas ${cdpLoading ? 'fa-spinner fa-spin' : 'fa-rotate'}`}></i> Refresh
                </button>
              </div>
            </div>
          </div>

          {!showingSubjectDetailPage && cdpData.subjects.length ? (
            <div className="metrics-grid selection-grid department-selection-grid mb-3 cdp-subject-grid">
              {cdpData.subjects.map((subject) => {
                const badge = getStatusBadge(subject.summary_status);
                const facultySummaries = (subject.faculty_statuses || []).filter((entry) => String(entry.faculty_name || '').trim());
                return (
                  <button
                    key={subject.id}
                    type="button"
                    className="metric-card selection-card-button cdp-subject-tile"
                    onClick={() => onLoadCdpOverview({
                      department: subject.department,
                      year: subject.year_level,
                      semester: subject.semester,
                      subject_id: subject.id,
                    })}
                  >
                    <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 10, marginBottom: 10 }}>
                      <div>
                        <div className="metric-label">{subject.subject_code}</div>
                        <div className="metric-value cdp-subject-title">{subject.subject_name}</div>
                      </div>
                      <span className={`badge ${badge.className}`}>{badge.label}</span>
                    </div>
                    <div className="cdp-subject-faculty-list">
                      {facultySummaries.length ? facultySummaries.map((faculty) => (
                        <div key={faculty.faculty_name} className="cdp-subject-faculty-row">
                          <span className="cdp-subject-faculty-name">{faculty.faculty_name}</span>
                          <span className="cdp-subject-faculty-pct">{faculty.completion_pct}%</span>
                        </div>
                      )) : (
                        <div className="selection-card-subtitle" style={{ marginTop: 2 }}>
                          {subject.faculty_name || 'Faculty details unavailable'}
                        </div>
                      )}
                    </div>
                    {subject.parser_error ? (
                      <div className="inline-muted" style={{ marginTop: 8, color: 'var(--danger)' }}>
                        {subject.parser_error}
                      </div>
                    ) : null}
                  </button>
                );
              })}
            </div>
          ) : !showingSubjectDetailPage ? (
            <div className="card">
              <div className="card-title"><i className="fas fa-circle-info"></i> No Subjects Configured</div>
              <div className="inline-muted" style={{ marginBottom: 12 }}>
                No subjects exist yet for <strong>{cdpData.selectedDepartment}</strong> / <strong>{formatYearLevel(cdpData.selectedYear || 1)}</strong> / <strong>{getSemesterLabel(cdpData.selectedSemester || '1')}</strong>.
              </div>
            </div>
          ) : null}

          {showingSubjectDetailPage && selectedSubject && selectedDetail ? (
            <>
              <div className="dashboard-dual-grid mb-3">
                <div className="card dashboard-status-card">
                  <div className="card-title"><i className="fas fa-book"></i> Subject Summary</div>
                  <div style={{ display: 'grid', gap: 8, fontSize: '.9rem' }}>
                    <div><strong>Code:</strong> {selectedSubject.subject_code}</div>
                    <div><strong>Subject:</strong> {selectedSubject.subject_name}</div>
                    <div><strong>Faculty:</strong> {selectedSubject.faculty_name}</div>
                    <div><strong>Status:</strong> <span className={`badge ${selectedStatusBadge.className}`}>{selectedStatusBadge.label}</span></div>
                    <div><strong>Scope:</strong> {selectedSubject.department} / {formatYearLevel(selectedSubject.year_level)} / {getSemesterLabel(selectedSubject.semester)}</div>
                    <div><strong>Academic Year:</strong> {selectedSubject.academic_start_year || '--'} - {selectedSubject.academic_end_year || '--'}</div>
                    <div><strong>Allocated Classes:</strong> {selectedSubject.class_sections.length ? selectedSubject.class_sections.join(', ') : '--'}</div>
                    <div><strong>Parsed:</strong> {formatDateTime(selectedDetail.parsed_at)}</div>
                  </div>
                </div>
                <div className="card dashboard-status-card">
                  <div className="card-title"><i className="fas fa-user-clock"></i> Defaulter Summary</div>
                  <div style={{ display: 'grid', gap: 8, fontSize: '.9rem' }}>
                    <div><strong>Faculty Count:</strong> {selectedDetail.faculty_count}</div>
                    <div><strong>Pending Faculty:</strong> {selectedDetail.pending_faculty_count}</div>
                    <div><strong>Pending Classes:</strong> {selectedDetail.pending_class_count}</div>
                    <div><strong>Pending Dates:</strong> {selectedDetail.pending_date_count}</div>
                    <div><strong>Completion:</strong> {selectedDetail.overall_completion_pct}%</div>
                    <div><strong>Today:</strong> {selectedDetail.today_pending ? 'Pending' : 'Ready'}</div>
                  </div>
                </div>
              </div>

              {selectedDetail.parser_error ? (
                <div className="card mb-3" style={{ border: '1px solid rgba(239,68,68,.35)', background: 'rgba(239,68,68,.08)' }}>
                  <div className="card-title"><i className="fas fa-triangle-exclamation"></i> Sheet Status Unavailable</div>
                  <div className="inline-muted">{selectedDetail.parser_error}</div>
                </div>
              ) : null}

              <div className="card mb-3">
                <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
                  <div className="card-title" style={{ marginBottom: 0, fontSize: '1.18rem' }}><i className="fas fa-user-check"></i> Faculty-wise Completion</div>
                  <div className="d-flex align-center flex-wrap" style={{ gap: 10 }}>
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => void handleCopySubjectDefaulters()}
                    >
                      <i className="fas fa-copy"></i> Copy Defaulters
                    </button>
                  </div>
                </div>
                <div className="d-flex flex-wrap align-center" style={{ gap: 10, marginBottom: 12 }}>
                  <select
                    className="form-control"
                    style={{ width: 210 }}
                    value={facultyFilter}
                    onChange={(event) => setFacultyFilter(event.target.value)}
                  >
                    <option value="__all__">All Faculty</option>
                    {facultyOptions.map((facultyName) => (
                      <option key={facultyName} value={facultyName}>{facultyName}</option>
                    ))}
                  </select>
                  <input
                    className="form-control"
                    style={{ width: 170 }}
                    type={facultyDateFrom || facultyDateFromFocused ? 'date' : 'text'}
                    placeholder="14/06/2026"
                    value={facultyDateFrom}
                    onFocus={() => setFacultyDateFromFocused(true)}
                    onBlur={() => setFacultyDateFromFocused(false)}
                    onChange={(event) => setFacultyDateFrom(event.target.value)}
                    aria-label="Filter from date"
                  />
                  <input
                    className="form-control"
                    style={{ width: 170 }}
                    type={facultyDateTo || facultyDateToFocused ? 'date' : 'text'}
                    placeholder="20/06/2026"
                    value={facultyDateTo}
                    onFocus={() => setFacultyDateToFocused(true)}
                    onBlur={() => setFacultyDateToFocused(false)}
                    onChange={(event) => setFacultyDateTo(event.target.value)}
                    aria-label="Filter to date"
                  />
                  {(facultyFilter !== '__all__' || facultyDateFrom || facultyDateTo) ? (
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => {
                        setFacultyFilter('__all__');
                        setFacultyDateFrom('');
                        setFacultyDateTo('');
                        setFacultyDateFromFocused(false);
                        setFacultyDateToFocused(false);
                      }}
                    >
                      <i className="fas fa-rotate-left"></i> Reset
                    </button>
                  ) : null}
                </div>
                {selectedDetail.faculty_statuses.length ? (
                  <div className="table-wrapper table-scroll-lg">
                    <table className="sticky-table">
                      <thead>
                        <tr>
                          <th>Faculty</th>
                          <th>Status</th>
                          <th>Completion</th>
                          <th>Completed Dates / Total Dates</th>
                          <th>Classes</th>
                          <th>Missing Entries</th>
                          <th>Pending Dates With Class</th>
                        </tr>
                      </thead>
                      <tbody>
                        {filteredFacultyStatuses.map((faculty) => {
                          const badge = getStatusBadge(faculty.status === 'error' ? 'error' : faculty.status);
                          return (
                            <tr key={faculty.faculty_name}>
                              <td>
                                <strong>{faculty.faculty_name}</strong>
                                {faculty.notes.length ? (
                                  <div className="inline-muted" style={{ fontSize: '.8rem', marginTop: 4 }}>{faculty.notes.join(' | ')}</div>
                                ) : null}
                              </td>
                              <td><span className={`badge ${badge.className}`}>{badge.label}</span></td>
                              <td>{faculty.completion_pct}%</td>
                              <td>{faculty.filled_cols} / {faculty.total_date_cols}</td>
                              <td>{faculty.class_sections.length ? faculty.class_sections.join(', ') : '--'}</td>
                              <td>{faculty.missing_entry_count}</td>
                              <td style={{ fontSize: '.82rem', color: 'var(--warning)', fontWeight: 700 }}>
                                {faculty.class_breakdown.some((item) => item.pending_dates.length) ? (
                                  faculty.class_breakdown
                                    .filter((item) => item.pending_dates.length)
                                    .map((item) => `${item.class_label}: ${item.pending_dates.join(', ')}`)
                                    .join(' | ')
                                ) : '--'}
                              </td>
                            </tr>
                          );
                        })}
                        {!filteredFacultyStatuses.length ? (
                          <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No faculty rows matched the current faculty and date-range filters.</td></tr>
                        ) : null}
                      </tbody>
                    </table>
                  </div>
                ) : (
                  <div className="panel-placeholder">No faculty allocations are available for this subject yet.</div>
                )}
              </div>

              <div className="card">
                <div className="card-title"><i className="fas fa-clipboard-check"></i> Class-wise Completion</div>
                {selectedDetail.classes.length ? (
                  <div className="table-wrapper table-scroll-lg">
                    <table className="sticky-table">
                      <thead>
                        <tr>
                          <th>Class</th>
                          <th>Completion</th>
                          <th>Completed Dates</th>
                          <th>Total Dates</th>
                          <th>Missing Entries</th>
                          <th>Today</th>
                          <th>Pending Dates</th>
                        </tr>
                      </thead>
                      <tbody>
                        {selectedDetail.classes.map((item) => (
                          <tr key={item.label}>
                            <td><strong>{item.label}</strong></td>
                            <td>{item.completion_pct}%</td>
                            <td>{item.filled_cols}</td>
                            <td>{item.total_date_cols}</td>
                            <td>{item.missing_entry_count}</td>
                            <td>
                              <span className={`badge ${item.today_col_exists ? (item.today_col_filled ? 'badge-success' : 'badge-warning') : 'badge-muted'}`}>
                                {!item.today_col_exists ? 'No Today Column' : item.today_col_filled ? 'Ready' : 'Pending'}
                              </span>
                            </td>
                            <td style={{ fontSize: '.82rem', color: 'var(--warning)', fontWeight: 700 }}>{item.pending_dates.length ? item.pending_dates.join(', ') : '--'}</td>
                          </tr>
                        ))}
                      </tbody>
                    </table>
                  </div>
                ) : (
                  <div className="panel-placeholder">No class-level attendance sections were detected in the linked sheet yet.</div>
                )}
              </div>
              {markEntrySection}
            </>
          ) : null}
        </>
      ) : null}
    </>
  );
}

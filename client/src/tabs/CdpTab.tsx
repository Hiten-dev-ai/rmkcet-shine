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
  force?: boolean;
};

type CdpTabProps = {
  cdpLoading: boolean;
  cdpData: CdpOverviewPayload | null;
  ScopeBreadcrumb: ComponentType<BreadcrumbProps>;
  formatYearLevel: (year: number) => string;
  formatDateTime: (value: string | null | undefined) => string;
  getSemesterLabel: (semester: string) => string;
  onLoadCdpOverview: (filters?: CdpFilters) => void;
  onRebuildScope: (filters: { department: string; year: number; semester: string; subject_id?: number | null; force?: boolean }) => void;
  onShowCopyDialog: (title: string, message: string) => void;
  onShowNoDefaultersNotice: (message: string) => void;
  copyTemplates: CdpCopyTemplates;
};

type MarkEntryTestKey = 'iat1' | 'iat2' | 'model' | 'unit_test';

type MarkEntryScope = Record<MarkEntryTestKey, boolean>;

type CdpCopyTemplates = {
  dailyAttendance: string;
  lecturePlan: string;
  markEntry: string;
};

type CdpCopyClassEntry = {
  facultyName: string;
  classLabel: string;
  pending: string;
};

type CdpCopySubjectBlock = {
  subjectLabel: string;
  scopeLabel: string;
  entries: CdpCopyClassEntry[];
};

function getStatusBadge(status: 'ready' | 'pending' | 'error' | 'unparsed') {
  if (status === 'ready') return { className: 'badge-success', label: 'Complete' };
  if (status === 'pending') return { className: 'badge-warning', label: 'Pending' };
  if (status === 'error') return { className: 'badge-danger', label: 'Sheet Error' };
  return { className: 'badge-muted', label: 'Not Parsed' };
}

const MARK_ENTRY_TEST_ORDER = ['iat1', 'iat2', 'model', 'unit_test'] as const;

const MARK_ENTRY_TEST_LABELS: Record<MarkEntryTestKey, string> = {
  iat1: 'IAT I',
  iat2: 'IAT II',
  model: 'Model',
  unit_test: 'Unit Test',
};

const DEFAULT_MARK_ENTRY_SCOPE: MarkEntryScope = {
  iat1: true,
  iat2: true,
  model: true,
  unit_test: true,
};

function getMarkEntryStatusBadge(status: 'complete' | 'pending' | 'not_available' | 'error') {
  if (status === 'complete') return { className: 'badge-success', label: 'Complete' };
  if (status === 'pending') return { className: 'badge-warning', label: 'Pending' };
  if (status === 'error') return { className: 'badge-danger', label: 'Error' };
  return { className: 'badge-muted', label: 'Not Available' };
}

function getLecturePlanStatusBadge(status: 'complete' | 'pending' | 'not_due' | 'sheet_issue') {
  if (status === 'complete') return { className: 'badge-success', label: 'Complete' };
  if (status === 'pending') return { className: 'badge-warning', label: 'Pending' };
  if (status === 'sheet_issue') return { className: 'badge-danger', label: 'Incomplete Data' };
  return { className: 'badge-muted', label: 'Not Due' };
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

function normalizeCopyOutput(text: string) {
  return String(text || '').replace(/[ \t]+\n/g, '\n').replace(/\n{3,}/g, '\n\n').trim();
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

type CdpCopySubject = {
  subject_code: string;
  subject_name: string;
  department: string;
  year_level: number;
  semester: string;
  parser_error?: string | null;
  faculty_statuses?: NonNullable<CdpOverviewPayload['selectedSubjectDetail']>['faculty_statuses'];
  lecture_plan?: NonNullable<CdpOverviewPayload['selectedSubjectDetail']>['lecture_plan'];
  mark_entry?: NonNullable<CdpOverviewPayload['selectedSubjectDetail']>['mark_entry'];
};

function createCopyBlock(subject: CdpCopySubject, entries: CdpCopyClassEntry[]): CdpCopySubjectBlock | null {
  if (!entries.length) return null;
  return {
    subjectLabel: `${subject.subject_code} - ${subject.subject_name}`,
    scopeLabel: buildSubjectScopeLabel(subject),
    entries,
  };
}

function buildDailyAttendanceBlock(subject: CdpCopySubject) {
  if (String(subject.parser_error || '').trim()) {
    return createCopyBlock(subject, [{ facultyName: 'Sheet', classLabel: 'Status', pending: `Sheet Error: ${subject.parser_error}` }]);
  }
  const entries: CdpCopyClassEntry[] = [];
  (subject.faculty_statuses || []).forEach((faculty) => {
    (faculty.class_breakdown || [])
      .filter((item) => item.pending_dates.length)
      .forEach((item) => {
        entries.push({
          facultyName: faculty.faculty_name || 'Faculty',
          classLabel: item.class_label || 'Class',
          pending: item.pending_dates.join(', '),
        });
      });
    if (!(faculty.class_breakdown || []).some((item) => item.pending_dates.length) && faculty.notes.length) {
      entries.push({
        facultyName: faculty.faculty_name || 'Faculty',
        classLabel: 'Sheet',
        pending: faculty.notes.join(' | '),
      });
    }
  });
  return createCopyBlock(subject, entries);
}

function getPendingLectureUnitLabel(unit: NonNullable<CdpCopySubject['lecture_plan']>['classes'][number]['units'][number]) {
  if (unit.status === 'not_due' || unit.status === 'complete') return '';
  if (unit.status === 'sheet_issue') return `Unit ${unit.unit} (Incomplete Data)`;
  return `Unit ${unit.unit}`;
}

function buildLecturePlanBlock(subject: CdpCopySubject) {
  const lecturePlan = subject.lecture_plan;
  if (!lecturePlan) return null;
  if (String(lecturePlan.parser_error || '').trim()) {
    return createCopyBlock(subject, [{ facultyName: 'Sheet', classLabel: 'Status', pending: `Sheet Error: ${lecturePlan.parser_error}` }]);
  }
  const entries: CdpCopyClassEntry[] = [];
  (lecturePlan.classes || []).forEach((classStatus) => {
    const pendingUnits = (classStatus.units || [])
      .map(getPendingLectureUnitLabel)
      .filter(Boolean);
    if (!pendingUnits.length) return;
    entries.push({
      facultyName: classStatus.faculty_name || 'Faculty',
      classLabel: classStatus.class_label || 'Class',
      pending: pendingUnits.join(', '),
    });
  });
  return createCopyBlock(subject, entries);
}

function buildMarkEntryBlock(subject: CdpCopySubject, markScope: MarkEntryScope) {
  const markEntry = subject.mark_entry;
  if (!markEntry?.rows?.length) return null;
  const entries: CdpCopyClassEntry[] = [];
  (markEntry.rows || []).forEach((row) => {
    const pendingTests = MARK_ENTRY_TEST_ORDER
      .filter((testKey) => markScope[testKey])
      .filter((testKey) => {
        const status = row.tests[testKey]?.status;
        return status === 'pending' || status === 'error';
      })
      .map((testKey) => MARK_ENTRY_TEST_LABELS[testKey]);
    if (!pendingTests.length) return;
    entries.push({
      facultyName: row.faculty_name || 'Faculty',
      classLabel: row.class_label || 'Class',
      pending: pendingTests.join(', '),
    });
  });
  return createCopyBlock(subject, entries);
}

function renderCdpBlocksAsEntries(blocks: CdpCopySubjectBlock[]) {
  const lines: string[] = [];
  blocks.forEach((block) => {
    lines.push(block.subjectLabel, block.scopeLabel, '');
    const groupedEntries = new Map<string, CdpCopyClassEntry[]>();
    block.entries.forEach((entry) => {
      const existing = groupedEntries.get(entry.facultyName) || [];
      existing.push(entry);
      groupedEntries.set(entry.facultyName, existing);
    });
    groupedEntries.forEach((entries, facultyName) => {
      lines.push(`${facultyName}:`);
      entries.forEach((entry) => lines.push(`${entry.classLabel}: ${entry.pending}`));
      lines.push('');
    });
  });
  return normalizeCopyOutput(lines.join('\n'));
}

function findTemplateLine(lines: string[], token: string, fallback: string) {
  return lines.find((line) => line.includes(token)) || fallback;
}

function renderCdpDetailedTemplate(
  template: string,
  blocks: CdpCopySubjectBlock[],
  count: number,
  scope: string,
) {
  const normalizedTemplate = String(template || '').replace(/\r\n/g, '\n');
  const legacyEntries = renderCdpBlocksAsEntries(blocks);
  if (normalizedTemplate.includes('{entries}')) {
    return normalizeCopyOutput(renderCopyTemplate(normalizedTemplate, {
      entries: legacyEntries,
      count: String(count),
      scope,
    }));
  }
  const lines = normalizedTemplate.split('\n');
  const detailedTokens = ['{subject}', '{faculty}', '{class}', '{pending}', '{next}'];
  const firstDetailIndex = lines.findIndex((line) => detailedTokens.some((token) => line.includes(token)));
  const headingLines = (firstDetailIndex >= 0 ? lines.slice(0, firstDetailIndex) : lines)
    .filter((line) => !line.includes('{scope}'));
  const subjectLine = findTemplateLine(lines, '{subject}', '{subject}');
  const scopeLine = findTemplateLine(lines, '{scope}', '{scope}');
  const facultyLine = findTemplateLine(lines, '{faculty}', '*{faculty}*:');
  const classLine = lines.find((line) => line.includes('{class}') || line.includes('{pending}')) || '{class}: {pending}';
  const output: string[] = [];
  const renderLine = (line: string, values: Record<string, string>) => renderCopyTemplate(line, {
    count: String(count),
    scope,
    ...values,
  });

  if (headingLines.length) output.push(renderLine(headingLines.join('\n'), {}), '');
  blocks.forEach((block, blockIndex) => {
    output.push(
      renderLine(subjectLine, { subject: block.subjectLabel, scope: block.scopeLabel }),
      renderLine(scopeLine, { subject: block.subjectLabel, scope: block.scopeLabel }),
      '',
    );
    const groupedEntries = new Map<string, CdpCopyClassEntry[]>();
    block.entries.forEach((entry) => {
      const existing = groupedEntries.get(entry.facultyName) || [];
      existing.push(entry);
      groupedEntries.set(entry.facultyName, existing);
    });
    groupedEntries.forEach((entries, facultyName) => {
      output.push(renderLine(facultyLine, { faculty: facultyName }));
      entries.forEach((entry) => {
        output.push(renderLine(classLine, {
          faculty: facultyName,
          class: entry.classLabel,
          pending: entry.pending,
        }));
      });
      output.push('');
    });
    if (blockIndex < blocks.length - 1) output.push('');
  });
  return normalizeCopyOutput(output.join('\n'));
}

function buildCdpSectionCopy(template: string, blocks: CdpCopySubjectBlock[], count: number, scope: string) {
  return renderCdpDetailedTemplate(template, blocks, count, scope).replace(/\n{3,}/g, '\n\n').trim();
}

function buildScopeSubjects(cdpData: CdpOverviewPayload): CdpCopySubject[] {
  return (cdpData.subjects || []).map((subject) => ({
    subject_code: subject.subject_code,
    subject_name: subject.subject_name,
    department: subject.department,
    year_level: subject.year_level,
    semester: subject.semester,
    parser_error: subject.parser_error,
    faculty_statuses: subject.faculty_statuses || [],
    lecture_plan: subject.lecture_plan,
    mark_entry: subject.mark_entry,
  }));
}

function buildSelectedSubjectCopySubject(
  subject: NonNullable<CdpOverviewPayload['selectedSubject']>,
  detail: NonNullable<CdpOverviewPayload['selectedSubjectDetail']>,
): CdpCopySubject {
  return {
    subject_code: subject.subject_code,
    subject_name: subject.subject_name,
    department: subject.department,
    year_level: subject.year_level,
    semester: subject.semester,
    parser_error: detail.parser_error,
    faculty_statuses: detail.faculty_statuses,
    lecture_plan: detail.lecture_plan,
    mark_entry: detail.mark_entry,
  };
}

function buildCombinedScopeDefaultersCopy(
  subjects: CdpCopySubject[],
  templates: CdpCopyTemplates,
  markScope: MarkEntryScope,
  scope: string,
) {
  const dailyBlocks = subjects.map(buildDailyAttendanceBlock).filter((block): block is CdpCopySubjectBlock => Boolean(block));
  const lectureBlocks = subjects.map(buildLecturePlanBlock).filter((block): block is CdpCopySubjectBlock => Boolean(block));
  const markBlocks = subjects.map((subject) => buildMarkEntryBlock(subject, markScope)).filter((block): block is CdpCopySubjectBlock => Boolean(block));
  return [
    dailyBlocks.length ? buildCdpSectionCopy(templates.dailyAttendance, dailyBlocks, dailyBlocks.length, scope) : '',
    lectureBlocks.length ? buildCdpSectionCopy(templates.lecturePlan, lectureBlocks, lectureBlocks.length, scope) : '',
    markBlocks.length ? buildCdpSectionCopy(templates.markEntry, markBlocks, markBlocks.length, scope) : '',
  ].filter(Boolean).join('\n\n').trim();
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
  copyTemplates,
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
  const [lecturePlanClassFilter, setLecturePlanClassFilter] = useState('__all__');
  const [lecturePlanStatusFilter, setLecturePlanStatusFilter] = useState('__all__');
  const [lecturePlanUnitFilter, setLecturePlanUnitFilter] = useState('__all__');
  const [markEntryScopeDialog, setMarkEntryScopeDialog] = useState<null | 'scope' | 'subject'>(null);
  const [markEntryCopyScope, setMarkEntryCopyScope] = useState<MarkEntryScope>(DEFAULT_MARK_ENTRY_SCOPE);

  useEffect(() => {
    setFacultyFilter('__all__');
    setFacultyDateFrom('');
    setFacultyDateTo('');
    setFacultyDateFromFocused(false);
    setFacultyDateToFocused(false);
    setLecturePlanClassFilter('__all__');
    setLecturePlanStatusFilter('__all__');
    setLecturePlanUnitFilter('__all__');
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
  const lecturePlan = selectedDetail?.lecture_plan || null;
  const lecturePlanBadge = getLecturePlanStatusBadge(lecturePlan?.status || 'not_due');
  const lecturePlanClassOptions = useMemo(() => (
    Array.from(new Set((lecturePlan?.classes || []).map((item) => item.class_label).filter(Boolean)))
  ), [lecturePlan]);
  const filteredLecturePlanClasses = useMemo(() => {
    const selectedUnit = lecturePlanUnitFilter === '__all__' ? null : Number(lecturePlanUnitFilter);
    return (lecturePlan?.classes || [])
      .filter((classStatus) => {
        if (lecturePlanClassFilter !== '__all__' && classStatus.class_label !== lecturePlanClassFilter) return false;
        return true;
      })
      .map((classStatus) => ({
        ...classStatus,
        units: classStatus.units.filter((unit) => (
          (!selectedUnit || unit.unit === selectedUnit)
          && (lecturePlanStatusFilter === '__all__' || unit.status === lecturePlanStatusFilter)
        )),
      }))
      .filter((classStatus) => classStatus.units.length);
  }, [lecturePlan, lecturePlanClassFilter, lecturePlanStatusFilter, lecturePlanUnitFilter]);

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
    <div className="card mt-3 cdp-subject-section cdp-mark-section">
      <div className="cdp-section-header">
        <div className="cdp-section-title-block">
          <div className="cdp-section-eyebrow">Mark Entry</div>
          <div className="cdp-section-title"><i className="fas fa-pen-to-square"></i> Internal Mark Entry</div>
          <div className="cdp-section-subtitle">Faculty-class completion across IAT, model, and unit-test marks.</div>
        </div>
        <div className="cdp-section-actions">
          <button
            type="button"
            className="btn btn-outline btn-sm"
            onClick={() => setMarkEntryScopeDialog('subject')}
          >
            <i className="fas fa-copy"></i> Copy Defaulters
          </button>
        </div>
      </div>
      <div className="cdp-summary-strip cdp-mark-summary-strip">
        {markEntrySummaries.map((summary) => {
          const badge = getMarkEntryStatusBadge(summary.status);
          return (
            <div key={summary.key} className="cdp-summary-tile cdp-test-summary-tile">
              <div className="d-flex justify-between align-center" style={{ gap: 10 }}>
                <strong>{summary.label}</strong>
                <span className={`badge ${badge.className}`}>{badge.label}</span>
              </div>
              <div className="inline-muted cdp-summary-subvalue">
                {summary.filled_students} / {summary.total_students} students
              </div>
              <div className="cdp-summary-value">
                {summary.completion_pct}% complete
              </div>
              {summary.message ? (
                <div className="inline-muted cdp-summary-message">
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

  const lecturePlanSection = selectedDetail ? (
    <div className="card mb-3 cdp-subject-section cdp-lecture-section">
      <div className="cdp-section-header">
        <div className="cdp-section-title-block">
          <div className="cdp-section-eyebrow">Lecture Plan</div>
          <div className="cdp-section-title">
            <i className="fas fa-chalkboard-user"></i> Proposed Lecture Plan
          </div>
          <div className="cdp-section-subtitle">Class and unit-wise plan health, daily completion, and unit-final metadata checks.</div>
        </div>
        <div className="cdp-section-actions">
          <span className={`badge ${lecturePlanBadge.className}`}>{lecturePlanBadge.label}</span>
          <button
            type="button"
            className="btn btn-outline btn-sm"
            onClick={() => void handleCopySubjectLecturePlanDefaulters()}
          >
            <i className="fas fa-copy"></i> Copy Defaulters
          </button>
        </div>
      </div>

      {lecturePlan?.parser_error ? (
        <div className="inline-muted" style={{ color: 'var(--danger)', marginBottom: 12 }}>
          {lecturePlan.parser_error}
        </div>
      ) : null}

      <div className="cdp-summary-strip">
        {[
          ['Classes Detected', String(lecturePlan?.classes_detected || 0)],
          ['Units Checked', String(lecturePlan?.units_checked || 0)],
          ['Due Rows Pending', String(lecturePlan?.due_rows_pending || 0)],
          ['Final Checks Pending', String(lecturePlan?.final_checkpoints_pending || 0)],
          ['Completion', `${lecturePlan?.completion_pct ?? 100}%`],
        ].map(([label, value]) => (
          <div key={label} className="cdp-summary-tile">
            <div className="metric-label">{label}</div>
            <div className="metric-value">{value}</div>
          </div>
        ))}
      </div>

      {lecturePlan?.classes?.length ? (
        <div className="cdp-filter-strip">
          <select
            className="form-control"
            value={lecturePlanClassFilter}
            onChange={(event) => setLecturePlanClassFilter(event.target.value)}
            aria-label="Filter lecture plan by class"
          >
            <option value="__all__">All Classes</option>
            {lecturePlanClassOptions.map((classLabel) => (
              <option key={classLabel} value={classLabel}>{classLabel}</option>
            ))}
          </select>
          <select
            className="form-control"
            value={lecturePlanStatusFilter}
            onChange={(event) => setLecturePlanStatusFilter(event.target.value)}
            aria-label="Filter lecture plan by status"
          >
            <option value="__all__">All Statuses</option>
            <option value="pending">Pending</option>
            <option value="sheet_issue">Incomplete Data</option>
            <option value="complete">Complete</option>
            <option value="not_due">Not Due</option>
          </select>
          <select
            className="form-control"
            value={lecturePlanUnitFilter}
            onChange={(event) => setLecturePlanUnitFilter(event.target.value)}
            aria-label="Filter lecture plan by unit"
          >
            <option value="__all__">All Units</option>
            {[1, 2, 3, 4, 5].map((unit) => (
              <option key={unit} value={unit}>Unit {unit}</option>
            ))}
          </select>
          {(lecturePlanClassFilter !== '__all__' || lecturePlanStatusFilter !== '__all__' || lecturePlanUnitFilter !== '__all__') ? (
            <button
              type="button"
              className="btn btn-outline btn-sm"
              onClick={() => {
                setLecturePlanClassFilter('__all__');
                setLecturePlanStatusFilter('__all__');
                setLecturePlanUnitFilter('__all__');
              }}
            >
              <i className="fas fa-rotate-left"></i> Reset
            </button>
          ) : null}
          <span className="inline-muted" style={{ fontSize: '.82rem' }}>
            Showing {filteredLecturePlanClasses.length} / {lecturePlan.classes.length} class{lecturePlan.classes.length === 1 ? '' : 'es'}
          </span>
        </div>
      ) : null}

      {lecturePlan?.classes?.length ? (
        <div className="cdp-lecture-class-list">
          {filteredLecturePlanClasses.map((classStatus) => {
            const classBadge = getLecturePlanStatusBadge(classStatus.status);
            return (
              <div key={`${classStatus.class_label}:${classStatus.faculty_name}`} className="cdp-lecture-class-block">
                <div className="cdp-class-block-header">
                  <div>
                    <strong className="cdp-class-title">{classStatus.class_label || 'Class'}</strong>
                    <div className="inline-muted" style={{ fontSize: '.82rem', marginTop: 2 }}>
                      {classStatus.faculty_name || 'Faculty'} - {classStatus.course_code || selectedSubject?.subject_code || '--'}
                    </div>
                  </div>
                  <div className="d-flex align-center flex-wrap" style={{ gap: 8 }}>
                    <span className={`badge ${classBadge.className}`}>{classBadge.label}</span>
                    <span className="inline-muted" style={{ fontSize: '.82rem' }}>{classStatus.completion_pct}%</span>
                  </div>
                </div>

                {classStatus.notes.length ? (
                  <div className="inline-muted" style={{ color: 'var(--warning)', fontSize: '.82rem', marginBottom: 10 }}>
                    {classStatus.notes.join(' | ')}
                  </div>
                ) : null}

                <div className="table-wrapper table-scroll-lg cdp-section-table-wrap">
                  <table className="sticky-table cdp-section-table">
                    <thead>
                      <tr>
                        <th>Unit</th>
                        <th>Status</th>
                        <th>Duration</th>
                        <th>Daily Due</th>
                        <th>Final Check</th>
                        <th>Completion</th>
                      </tr>
                    </thead>
                    <tbody>
                      {classStatus.units.map((unit) => {
                        const unitBadge = getLecturePlanStatusBadge(unit.status);
                        const dailyCompletedRows = Math.max(0, Number(unit.due_row_count || 0) - Number(unit.pending_row_count || 0));
                        const finalIssuePreview = unit.final_issues.flatMap((issue) => [
                          ...issue.missing_fields,
                          ...issue.missing_row_fields.slice(0, 2).map((rowIssue) => `Row ${rowIssue.serial || rowIssue.row_number}: ${rowIssue.missing_fields.join(', ')}`),
                        ]).slice(0, 4);
                        return (
                          <tr key={`${classStatus.class_label}:unit:${unit.unit}`}>
                            <td>
                              <strong>Unit {unit.unit}</strong>
                            </td>
                            <td><span className={`badge ${unitBadge.className}`}>{unitBadge.label}</span></td>
                            <td style={{ fontSize: '.82rem' }}>
                              <strong>From:</strong> {unit.from_date || '--'}<br />
                              <strong>To:</strong> {unit.to_date || '--'}
                              {unit.notes.length ? (
                                <div className="inline-muted" style={{ color: 'var(--warning)', marginTop: 4 }}>
                                  {unit.notes.join(' | ')}
                                </div>
                              ) : null}
                            </td>
                            <td style={{ fontSize: '.82rem' }}>
                              <div><strong>{dailyCompletedRows}</strong> / <strong>{unit.due_row_count}</strong> due rows completed</div>
                            </td>
                            <td style={{ fontSize: '.82rem' }}>
                              <span className={`badge ${unit.final_due ? (unit.final_issues.length ? 'badge-warning' : 'badge-success') : 'badge-muted'}`}>
                                {unit.final_due ? (unit.final_issues.length ? 'Pending' : 'Complete') : 'Not Due'}
                              </span>
                              {finalIssuePreview.length ? (
                                <div className="inline-muted" style={{ color: 'var(--warning)', marginTop: 4 }}>
                                  {finalIssuePreview.join(' | ')}
                                </div>
                              ) : null}
                            </td>
                            <td style={{ fontSize: '.82rem' }}>
                              <strong>{unit.completion_pct}%</strong>
                            </td>
                          </tr>
                        );
                      })}
                      {!classStatus.units.length ? (
                        <tr><td colSpan={6} className="text-center text-muted" style={{ padding: 18 }}>No units were detected for this class.</td></tr>
                      ) : null}
                    </tbody>
                  </table>
                </div>
              </div>
            );
          })}
          {!filteredLecturePlanClasses.length ? (
            <div className="panel-placeholder">No Proposed Lecture Plan units matched the current filters.</div>
          ) : null}
        </div>
      ) : (
        <div className="panel-placeholder">Proposed Lecture Plan rows will appear after the linked sheet is parsed.</div>
      )}
    </div>
  ) : null;

  async function handleCopyScopeDefaulters() {
    if (!cdpData) return;
    try {
      const subjects = buildScopeSubjects(cdpData);
      const copiedText = buildCombinedScopeDefaultersCopy(
        subjects,
        copyTemplates,
        markEntryCopyScope,
        `${cdpData.selectedDepartment} / ${formatYearLevel(cdpData.selectedYear || 1)} / ${getSemesterLabel(cdpData.selectedSemester || '1')}`,
      );
      if (!copiedText) {
        onShowNoDefaultersNotice('No defaulters were found for the selected CDP scope.');
        return;
      }
      await copyText(copiedText);
      onShowCopyDialog(
        'Copied',
        `Copied CDP defaulters from ${cdpData.selectedDepartment} / ${formatYearLevel(cdpData.selectedYear || 1)} / ${getSemesterLabel(cdpData.selectedSemester || '1')}.`,
      );
    } catch {
      onShowCopyDialog('Copy Failed', 'Unable to copy CDP defaulters right now.');
    } finally {
      setMarkEntryScopeDialog(null);
    }
  }

  async function handleCopySubjectDailyAttendanceDefaulters() {
    if (!selectedSubject || !selectedDetail) return;
    try {
      const subject = buildSelectedSubjectCopySubject(selectedSubject, selectedDetail);
      const block = buildDailyAttendanceBlock(subject);
      if (!block) {
        onShowNoDefaultersNotice(`No daily attendance defaulters were found for ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`);
        return;
      }
      const copiedText = buildCdpSectionCopy(copyTemplates.dailyAttendance, [block], 1, buildSubjectScopeLabel(selectedSubject));
      await copyText(copiedText);
      onShowCopyDialog(
        'Copied',
        `Copied daily attendance defaulters from ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`,
      );
    } catch {
      onShowCopyDialog('Copy Failed', 'Unable to copy CDP defaulters right now.');
    }
  }

  async function handleCopySubjectLecturePlanDefaulters() {
    if (!selectedSubject || !selectedDetail) return;
    try {
      const subject = buildSelectedSubjectCopySubject(selectedSubject, selectedDetail);
      const block = buildLecturePlanBlock(subject);
      if (!block) {
        onShowNoDefaultersNotice(`No proposed lecture plan defaulters were found for ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`);
        return;
      }
      const copiedText = buildCdpSectionCopy(copyTemplates.lecturePlan, [block], 1, buildSubjectScopeLabel(selectedSubject));
      await copyText(copiedText);
      onShowCopyDialog('Copied', `Copied proposed lecture plan defaulters from ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`);
    } catch {
      onShowCopyDialog('Copy Failed', 'Unable to copy CDP lecture plan defaulters right now.');
    }
  }

  async function handleCopySubjectMarkEntryDefaulters() {
    if (!selectedSubject || !selectedDetail) return;
    try {
      const subject = buildSelectedSubjectCopySubject(selectedSubject, selectedDetail);
      const block = buildMarkEntryBlock(subject, markEntryCopyScope);
      if (!block) {
        onShowNoDefaultersNotice(`No internal mark entry defaulters were found for ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`);
        return;
      }
      const copiedText = buildCdpSectionCopy(copyTemplates.markEntry, [block], 1, buildSubjectScopeLabel(selectedSubject));
      await copyText(copiedText);
      onShowCopyDialog('Copied', `Copied internal mark entry defaulters from ${selectedSubject.subject_code} - ${selectedSubject.subject_name}.`);
    } catch {
      onShowCopyDialog('Copy Failed', 'Unable to copy CDP mark entry defaulters right now.');
    } finally {
      setMarkEntryScopeDialog(null);
    }
  }

  function handleConfirmMarkEntryScope() {
    if (markEntryScopeDialog === 'scope') {
      void handleCopyScopeDefaulters();
    } else if (markEntryScopeDialog === 'subject') {
      void handleCopySubjectMarkEntryDefaulters();
    }
  }

  if (cdpLoading && !cdpData) {
    return (
      <div className="card">
        <div className="panel-placeholder">Loading CDP workspace...</div>
      </div>
    );
  }

  return (
    <>
      {markEntryScopeDialog ? (
        <div className="modal-overlay open" onClick={() => setMarkEntryScopeDialog(null)}>
          <div className="modal cdp-mark-scope-modal" onClick={(event) => event.stopPropagation()}>
            <div className="modal-header">
              <div>
                <h3>Internal Mark Entry Scope</h3>
                <div className="inline-muted" style={{ fontSize: '.84rem', marginTop: 4 }}>
                  Choose which tests are due before copying CDP mark-entry defaulters.
                </div>
              </div>
              <button className="modal-close" type="button" onClick={() => setMarkEntryScopeDialog(null)}>
                <i className="fas fa-xmark"></i>
              </button>
            </div>
            <div className="cdp-mark-scope-list">
              {MARK_ENTRY_TEST_ORDER.map((testKey) => (
                <label key={testKey} className="settings-slider-row">
                  <span>
                    <strong>{MARK_ENTRY_TEST_LABELS[testKey]}</strong>
                    <small>Include pending rows for {MARK_ENTRY_TEST_LABELS[testKey]}.</small>
                  </span>
                  <span className="settings-slider">
                    <input
                      type="checkbox"
                      checked={markEntryCopyScope[testKey]}
                      onChange={(event) => setMarkEntryCopyScope((prev) => ({ ...prev, [testKey]: event.target.checked }))}
                    />
                    <span className="settings-slider-track"></span>
                  </span>
                </label>
              ))}
            </div>
            <div className="btn-group justify-end" style={{ marginTop: 16 }}>
              <button type="button" className="btn btn-outline" onClick={() => setMarkEntryScopeDialog(null)}>
                Cancel
              </button>
              <button
                type="button"
                className="btn btn-primary"
                disabled={!MARK_ENTRY_TEST_ORDER.some((testKey) => markEntryCopyScope[testKey])}
                onClick={handleConfirmMarkEntryScope}
              >
                <i className="fas fa-copy"></i> Copy
              </button>
            </div>
          </div>
        </div>
      ) : null}
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
                onClick={() => onLoadCdpOverview({
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
                    onClick={() => setMarkEntryScopeDialog('scope')}
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
                    force: true,
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
              <div className="card dashboard-status-card mb-3 cdp-subject-summary-card">
                <div className="cdp-section-header">
                  <div className="cdp-section-title-block">
                    <div className="cdp-section-eyebrow">Subject Workspace</div>
                    <div className="cdp-section-title"><i className="fas fa-book"></i> Subject Summary</div>
                    <div className="cdp-section-subtitle">Attendance, proposed lecture plan, and mark-entry completion for this subject.</div>
                  </div>
                  <span className={`badge ${selectedStatusBadge.className}`}>{selectedStatusBadge.label}</span>
                </div>
                <div className="cdp-subject-summary-grid">
                  <div className="cdp-summary-field">
                    <span>Subject</span>
                    <strong>{selectedSubject.subject_name}</strong>
                  </div>
                  <div className="cdp-summary-field">
                    <span>Faculty</span>
                    <strong>{selectedSubject.faculty_name}</strong>
                  </div>
                  <div className="cdp-summary-field">
                    <span>Academic Year</span>
                    <strong>{selectedSubject.academic_start_year || '--'} - {selectedSubject.academic_end_year || '--'}</strong>
                  </div>
                  <div className="cdp-summary-field">
                    <span>Allocated Classes</span>
                    <strong>{selectedSubject.class_sections.length ? selectedSubject.class_sections.join(', ') : '--'}</strong>
                  </div>
                  <div className="cdp-summary-field">
                    <span>Pending Faculty</span>
                    <strong>{selectedDetail.pending_faculty_count}</strong>
                  </div>
                  <div className="cdp-summary-field">
                    <span>Pending Classes</span>
                    <strong>{selectedDetail.pending_class_count}</strong>
                  </div>
                  <div className="cdp-summary-field">
                    <span>Pending Dates</span>
                    <strong>{selectedDetail.pending_date_count}</strong>
                  </div>
                  <div className="cdp-summary-field">
                    <span>Today</span>
                    <strong>{selectedDetail.today_pending ? 'Pending' : 'Ready'}</strong>
                  </div>
                </div>
              </div>

              {selectedDetail.parser_error ? (
                <div className="card mb-3" style={{ border: '1px solid rgba(239,68,68,.35)', background: 'rgba(239,68,68,.08)' }}>
                  <div className="card-title"><i className="fas fa-triangle-exclamation"></i> Sheet Status Unavailable</div>
                  <div className="inline-muted">{selectedDetail.parser_error}</div>
                </div>
              ) : null}

              <div className="card mb-3 cdp-subject-section cdp-attendance-section">
                <div className="cdp-section-header">
                  <div className="cdp-section-title-block">
                    <div className="cdp-section-eyebrow">Daily Attendance</div>
                    <div className="cdp-section-title"><i className="fas fa-user-check"></i> Faculty-wise Completion</div>
                    <div className="cdp-section-subtitle">Filter faculty defaulters by owner and pending attendance dates.</div>
                  </div>
                  <div className="cdp-section-actions">
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => void handleCopySubjectDailyAttendanceDefaulters()}
                    >
                      <i className="fas fa-copy"></i> Copy Defaulters
                    </button>
                  </div>
                </div>
                <div className="cdp-filter-strip">
                  <select
                    className="form-control"
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
                  <div className="table-wrapper table-scroll-lg cdp-section-table-wrap">
                    <table className="sticky-table cdp-section-table">
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

              <div className="card mb-3 cdp-subject-section cdp-class-section">
                <div className="cdp-section-header">
                  <div className="cdp-section-title-block">
                    <div className="cdp-section-eyebrow">Daily Attendance</div>
                    <div className="cdp-section-title"><i className="fas fa-clipboard-check"></i> Class-wise Completion</div>
                    <div className="cdp-section-subtitle">Class-level attendance readiness and pending date columns.</div>
                  </div>
                </div>
                {selectedDetail.classes.length ? (
                  <div className="table-wrapper table-scroll-lg cdp-section-table-wrap">
                    <table className="sticky-table cdp-section-table">
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
                                {!item.today_col_exists ? 'No Periods' : item.today_col_filled ? 'Ready' : 'Pending'}
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
              {lecturePlanSection}
              {markEntrySection}
            </>
          ) : null}
        </>
      ) : null}
    </>
  );
}

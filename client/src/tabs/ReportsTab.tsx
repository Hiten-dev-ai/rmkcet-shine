import { useMemo, type ComponentType, type FormEvent } from 'react';
import type {
  AppConfig,
  AuthUser,
  CounselorVisibleTestRecord,
  ReportStudentRow,
  ReportTestRecord,
  ReportsOverviewPayload,
  TestDetailPayload,
} from '../types';

type BreadcrumbProps = {
  icon: string;
  items: Array<{ label: string; onClick?: () => void }>;
};

type TestMetaDraft = {
  test_name: string;
  semester: string;
  batch_name: string;
  section: string;
};

type ReportUploadDraft = {
  test_name: string;
  semester: string;
  batch_name: string;
  section: string;
  upload_mode: string;
  file: File | null;
};

type SemesterBuckets<T> = {
  sem1: T[];
  sem2: T[];
};

type ReportsTabProps = {
  currentUser: AuthUser;
  appConfig: AppConfig | null;
  testDetailLoading: boolean;
  testDetail: TestDetailPayload | null;
  testDetailSearch: string;
  testDetailSort: string;
  visibleTestDetailStudents: ReportStudentRow[];
  testMetaDraft: TestMetaDraft;
  testMetaReadOnly: boolean;
  testMarksReadOnly: boolean;
  savingMeta: boolean;
  savingMarks: boolean;
  counselorTestsLoading: boolean;
  counselorTestsBySemester: SemesterBuckets<CounselorVisibleTestRecord>;
  reportsLoading: boolean;
  reportsData: ReportsOverviewPayload | null;
  reportTestsBySemester: SemesterBuckets<ReportTestRecord>;
  reportUploadDraft: ReportUploadDraft;
  reportUploadInputKey: number;
  uploadingReport: boolean;
  ScopeBreadcrumb: ComponentType<BreadcrumbProps>;
  formatYearLevel: (year: number) => string;
  formatUploadDateTime: (value: string | null | undefined) => string;
  getDefaultBatchNameForYearLevel: (year: number, config: AppConfig | null) => string;
  readSummaryMetric: (marks: Record<string, string>, keys: string[]) => string;
  onBackFromTestDetail: () => void;
  onTestDetailSearchChange: (value: string) => void;
  onTestDetailSortChange: (value: string) => void;
  onSaveAllMarks: () => void;
  onTestMetaDraftChange: (field: keyof TestMetaDraft, value: string) => void;
  onSaveMetaSubmit: (event: FormEvent<HTMLFormElement>) => void;
  onUpdateLocalMark: (regNo: string, subject: string, value: string) => void;
  onSaveRowMarks: (regNo: string) => void;
  isTestDetailRowDirty: (regNo: string) => boolean;
  onLoadTestDetail: (testId: number) => void;
  onStartCounselorSendFlow: (testId: number, testName: string) => void;
  sendResultOpeningId?: number | null;
  onLoadReports: (department?: string, year?: number | null) => void;
  onUploadReportSubmit: (event: FormEvent<HTMLFormElement>) => void;
  onReportUploadDraftChange: (field: 'test_name' | 'semester' | 'upload_mode', value: string) => void;
  onReportUploadFileChange: (file: File | null) => void;
  onToggleTestBlock: (test: ReportTestRecord) => void;
  onDeleteTest: (test: ReportTestRecord) => void;
};

function CounselorTestsTable({
  title,
  tests,
  counselorTestsLoading,
  currentUser,
  formatYearLevel,
  onLoadTestDetail,
  onStartCounselorSendFlow,
  sendResultOpeningId,
}: {
  title: string;
  tests: CounselorVisibleTestRecord[];
  counselorTestsLoading: boolean;
  currentUser: AuthUser;
  formatYearLevel: (year: number) => string;
  onLoadTestDetail: (testId: number) => void;
  onStartCounselorSendFlow: (testId: number, testName: string) => void;
  sendResultOpeningId?: number | null;
}) {
  return (
    <div className="card mb-3" data-tour-id={currentUser.role === 'counselor' ? 'counselor-reports' : undefined}>
      <div className="card-title"><i className="fas fa-database"></i> {title}</div>
      <div className="table-wrapper">
        <table>
          <thead>
            <tr>
              <th>Test Name</th>
              <th>Year</th>
              <th>Batch</th>
              <th>Sem</th>
              <th>Students</th>
              <th>Status</th>
              <th>Actions</th>
            </tr>
          </thead>
          <tbody>
            {counselorTestsLoading ? (
              <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading tests...</td></tr>
            ) : tests.length ? tests.map((test) => (
              <tr key={test.id}>
                <td><strong>{test.test_name}</strong></td>
                <td>{formatYearLevel(test.year_level || (currentUser.year_level || 1))}</td>
                <td>{test.batch_name || '-'}</td>
                <td>{test.semester || '-'}</td>
                <td><span className="badge badge-info">{test.student_count}</span></td>
                <td>
                  {test.is_blocked ? (
                    <span className="badge badge-danger">Blocked By Admin</span>
                  ) : (test.generated_count || 0) > 0 ? (
                    <span className="badge badge-success">Uploaded</span>
                  ) : (
                    <span className="badge badge-warning">Upload Pending</span>
                  )}
                </td>
                <td>
                  <div className="btn-group">
                    <button type="button" className="btn btn-outline btn-sm" onClick={() => onLoadTestDetail(test.id)} disabled={Boolean(test.is_blocked)}>
                      <i className="fas fa-eye"></i> View/Edit
                    </button>
                    <button type="button" className="btn btn-primary btn-sm" data-tour-id="counselor-send-entry" onClick={() => onStartCounselorSendFlow(test.id, test.test_name)} disabled={Boolean(test.is_blocked) || sendResultOpeningId === test.id}>
                      <i className={`fas ${sendResultOpeningId === test.id ? 'fa-spinner fa-spin' : 'fa-paper-plane'}`}></i> {sendResultOpeningId === test.id ? 'Opening...' : 'Send Results'}
                    </button>
                  </div>
                </td>
              </tr>
            )) : (
              <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No {title.toLowerCase()} tests mapped yet.</td></tr>
            )}
          </tbody>
        </table>
      </div>
    </div>
  );
}

function ReportTestsTable({
  title,
  tests,
  reportsLoading,
  currentUser,
  formatUploadDateTime,
  onLoadTestDetail,
  onToggleTestBlock,
  onDeleteTest,
}: {
  title: string;
  tests: ReportTestRecord[];
  reportsLoading: boolean;
  currentUser: AuthUser;
  formatUploadDateTime: (value: string | null | undefined) => string;
  onLoadTestDetail: (testId: number) => void;
  onToggleTestBlock: (test: ReportTestRecord) => void;
  onDeleteTest: (test: ReportTestRecord) => void;
}) {
  return (
    <div className="card mb-3">
      <div className="card-title"><i className="fas fa-database"></i> {title}</div>
      <div className="table-wrapper table-scroll-lg">
        <table className="sticky-table">
          <thead>
            <tr>
              <th>Test Name</th>
              <th>Batch</th>
              <th>Semester</th>
              <th>Uploaded By</th>
              <th>Students</th>
              <th>Uploaded At</th>
              <th>Actions</th>
            </tr>
          </thead>
          <tbody>
            {reportsLoading ? (
              <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>Loading reports...</td></tr>
            ) : tests.length ? tests.map((test) => (
              <tr key={test.id}>
                <td><strong>{test.test_name || `Test #${test.id}`}</strong></td>
                <td>{test.batch_name || '-'}</td>
                <td>{test.semester || '-'}</td>
                <td><span style={{ fontSize: '.85rem' }}>{test.uploaded_by_name || test.uploaded_by || '-'}</span></td>
                <td><span className="badge badge-info">{test.student_count || 0}</span></td>
                <td style={{ fontSize: '.82rem' }}>{formatUploadDateTime(test.uploaded_at)}</td>
                <td>
                  <div className="btn-group">
                    <button
                      type="button"
                      className="btn btn-outline btn-sm"
                      onClick={() => onLoadTestDetail(test.id)}
                    >
                      <i className={`fas ${currentUser.role === 'principal' ? 'fa-eye' : 'fa-pen'}`}></i> {currentUser.role === 'principal' ? 'View' : 'Edit/View'}
                    </button>
                    {currentUser.role !== 'principal' ? (
                      <>
                        <button type="button" className={`btn ${test.is_blocked ? 'btn-success' : 'btn-warning'} btn-sm`} onClick={() => onToggleTestBlock(test)}>
                          <i className={`fas ${test.is_blocked ? 'fa-lock-open' : 'fa-lock'}`}></i>
                        </button>
                        <button type="button" className="btn btn-danger btn-sm" onClick={() => onDeleteTest(test)}>
                          <i className="fas fa-trash"></i>
                        </button>
                      </>
                    ) : null}
                  </div>
                </td>
              </tr>
            )) : (
              <tr><td colSpan={7} className="text-center text-muted" style={{ padding: 24 }}>No {title.toLowerCase()} tests uploaded yet.</td></tr>
            )}
          </tbody>
        </table>
      </div>
    </div>
  );
}

function buildSectionHeading(student: ReportStudentRow, fallbackDepartment: string, fallbackSection: string) {
  const studentSection = String(student.section || '').trim();
  const department = String(student.department || fallbackDepartment || '').trim().toUpperCase();
  const normalizedStudentSection = studentSection.toUpperCase();
  if (normalizedStudentSection) {
    if (!department) return normalizedStudentSection;
    if (normalizedStudentSection === department || normalizedStudentSection.startsWith(`${department} `)) {
      return normalizedStudentSection;
    }
    return `${department} ${normalizedStudentSection}`.trim();
  }

  const normalizedFallbackSection = String(fallbackSection || '').trim().toUpperCase();
  if (normalizedFallbackSection) {
    if (!department) return normalizedFallbackSection;
    if (normalizedFallbackSection === department || normalizedFallbackSection.startsWith(`${department} `)) {
      return normalizedFallbackSection;
    }
    return `${department} ${normalizedFallbackSection}`.trim();
  }

  return department ? `${department} Students` : 'All Students';
}

export default function ReportsTab({
  currentUser,
  appConfig,
  testDetailLoading,
  testDetail,
  testDetailSearch,
  testDetailSort,
  visibleTestDetailStudents,
  testMetaDraft,
  testMetaReadOnly,
  testMarksReadOnly,
  savingMeta,
  savingMarks,
  counselorTestsLoading,
  counselorTestsBySemester,
  reportsLoading,
  reportsData,
  reportTestsBySemester,
  reportUploadDraft,
  reportUploadInputKey,
  uploadingReport,
  ScopeBreadcrumb,
  formatYearLevel,
  formatUploadDateTime,
  getDefaultBatchNameForYearLevel,
  readSummaryMetric,
  onBackFromTestDetail,
  onTestDetailSearchChange,
  onTestDetailSortChange,
  onSaveAllMarks,
  onTestMetaDraftChange,
  onSaveMetaSubmit,
  onUpdateLocalMark,
  onSaveRowMarks,
  isTestDetailRowDirty,
  onLoadTestDetail,
  onStartCounselorSendFlow,
  sendResultOpeningId,
  onLoadReports,
  onUploadReportSubmit,
  onReportUploadDraftChange,
  onReportUploadFileChange,
  onToggleTestBlock,
  onDeleteTest,
}: ReportsTabProps) {
  const testDetailSectionGroups = useMemo(() => {
    if (!testDetail || !visibleTestDetailStudents.length) return [];

    const buckets = new Map<string, { heading: string; students: ReportStudentRow[] }>();
    for (const student of visibleTestDetailStudents) {
      const heading = buildSectionHeading(student, testDetail.meta.department || '', testDetail.meta.section || '');
      const key = heading.toUpperCase();
      if (!buckets.has(key)) {
        buckets.set(key, { heading, students: [] });
      }
      buckets.get(key)!.students.push(student);
    }

    return Array.from(buckets.values());
  }, [testDetail, visibleTestDetailStudents]);
  const testDetailAvailableSectionsText = useMemo(() => {
    if (!testDetail) return '';
    const labels = Array.from(
      new Set(
        testDetailSectionGroups
          .map((group) => String(group.heading || '').trim())
          .filter(Boolean),
      ),
    );
    if (labels.length) return labels.join(', ');
    return String(testDetail.meta.section || '').trim();
  }, [testDetail, testDetailSectionGroups]);

  if (testDetailLoading) {
    return (
      <div className="card">
        <div className="panel-placeholder">Loading test details...</div>
      </div>
    );
  }

  if (testDetail) {
    return (
      <div className="report-page-shell">
        <div className="report-sticky-toolbar report-detail-toolbar mb-2">
          <div className="report-toolbar-top">
            <button
              type="button"
              className="btn btn-outline btn-sm report-back-btn"
              onClick={onBackFromTestDetail}
            >
              <i className="fas fa-arrow-left"></i> {currentUser.role === 'counselor' ? 'Back To Test Database' : 'Back To Reports'}
            </button>
          </div>
          <div className="report-toolbar-main">
            <div className="report-toolbar-cluster report-toolbar-search">
              <div className="form-group report-toolbar-field">
                <label className="form-label">Search Students</label>
                <input
                  className="form-control"
                  placeholder="Search by reg no or student name"
                  value={testDetailSearch}
                  onChange={(event) => onTestDetailSearchChange(event.target.value)}
                />
              </div>
              <div className="form-group report-toolbar-field report-toolbar-field-sm">
                <label className="form-label">Sort</label>
                <select className="form-control" value={testDetailSort} onChange={(event) => onTestDetailSortChange(event.target.value)}>
                  <option value="reg_asc">Reg No</option>
                  <option value="reg_desc">Reg No (Desc)</option>
                  <option value="name_asc">Name (A-Z)</option>
                  <option value="name_desc">Name (Z-A)</option>
                  <option value="gpa_desc">GPA (High-Low)</option>
                  <option value="gpa_asc">GPA (Low-High)</option>
                  <option value="failed_desc">Failed (High-Low)</option>
                  <option value="failed_asc">Failed (Low-High)</option>
                </select>
              </div>
            </div>
            <div className="report-toolbar-cluster report-toolbar-end">
              {!testMarksReadOnly ? (
                <button className="btn btn-primary report-save-all-btn" type="button" onClick={onSaveAllMarks} disabled={savingMarks}>
                  <i className="fas fa-save"></i> {savingMarks ? 'Saving...' : 'Save All Marks'}
                </button>
              ) : null}
              <span className="badge badge-info">{testDetail.meta.test_name || 'Selected Test'}</span>
            </div>
          </div>
        </div>

        <div className="card mb-3">
          <div className="card-title"><i className="fas fa-pen"></i> Test Metadata</div>
          <form onSubmit={onSaveMetaSubmit}>
            <div className="form-row">
              <div className="form-group">
                <label className="form-label">Test Name</label>
                <select
                  className="form-control"
                  value={testMetaDraft.test_name}
                  disabled={testMetaReadOnly}
                  onChange={(event) => onTestMetaDraftChange('test_name', event.target.value)}
                >
                  <option value="IAT 1">IAT 1</option>
                  <option value="IAT 2">IAT 2</option>
                  <option value="MODEL EXAM">MODEL EXAM</option>
                </select>
              </div>
              <div className="form-group">
                <label className="form-label">Semester</label>
                <input
                  type="text"
                  className="form-control"
                  value={testMetaDraft.semester}
                  readOnly={testMetaReadOnly}
                  onChange={(event) => onTestMetaDraftChange('semester', event.target.value)}
                />
              </div>
              <div className="form-group">
                <label className="form-label">Section</label>
                <input
                  type="text"
                  className="form-control"
                  value={testDetailAvailableSectionsText || '-'}
                  readOnly
                  placeholder="Available sections"
                />
              </div>
              <div className="form-group">
                <label className="form-label">Batch</label>
                <input
                  type="text"
                  className="form-control"
                  value={testMetaDraft.batch_name}
                  readOnly={testMetaReadOnly}
                  onChange={(event) => onTestMetaDraftChange('batch_name', event.target.value)}
                />
              </div>
              <div className="form-group">
                <label className="form-label">Department</label>
                <input className="form-control" value={testDetail.meta.department || '-'} readOnly />
              </div>
              <div className="form-group">
                <label className="form-label">Year</label>
                <input className="form-control" value={formatYearLevel(testDetail.meta.year_level || 1)} readOnly />
              </div>
            </div>
            {!testMetaReadOnly ? (
              <button className="btn btn-primary" type="submit" disabled={savingMeta}>
                <i className="fas fa-save"></i> {savingMeta ? 'Saving...' : 'Save Metadata'}
              </button>
            ) : null}
          </form>
        </div>

        <div className="card">
          <div className="card-title">
            <span><i className="fas fa-table"></i> Student Marks</span>
          </div>
          {testDetailSectionGroups.length ? testDetailSectionGroups.map((group) => (
            <div key={group.heading} className="mb-3">
              <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 10 }}>
                <strong style={{ fontSize: '.96rem' }}>{group.heading}</strong>
                <span className="badge badge-info">{group.students.length} students</span>
              </div>
              <div className="table-wrapper report-marks-scroll">
                <table className="report-marks-table">
                  <thead>
                    <tr>
                      <th>Reg No</th>
                      <th>Student Name</th>
                      {testDetail.subjects.map((subject) => (
                        <th key={subject}>{subject}</th>
                      ))}
                      <th>GPA</th>
                      <th className="summary-col-failed">Failed</th>
                      {!testMarksReadOnly ? <th>Action</th> : null}
                    </tr>
                  </thead>
                  <tbody>
                    {group.students.map((student) => (
                      <tr key={`${group.heading}:${student.reg_no}`}>
                        <td><strong>{student.reg_no}</strong></td>
                        <td>{student.student_name || '-'}</td>
                        {testDetail.subjects.map((subject) => (
                          <td key={`${group.heading}:${student.reg_no}:${subject}`}>
                            {testMarksReadOnly ? (
                              student.marks[subject] || ''
                            ) : (
                              <input
                                className="form-control"
                                value={student.marks[subject] || ''}
                                style={{ minWidth: 80 }}
                                onChange={(event) => onUpdateLocalMark(student.reg_no, subject, event.target.value)}
                              />
                            )}
                          </td>
                        ))}
                        <td>{readSummaryMetric(student.marks, ['GPA', 'gpa', 'CGPA', 'cgpa'])}</td>
                        <td className="summary-col-failed">{readSummaryMetric(student.marks, ['No. of subjects failed', 'noofsubjectsfailed', 'failedsubjects'])}</td>
                        {!testMarksReadOnly ? (
                          <td>
                            <button
                              className={`btn btn-sm ${isTestDetailRowDirty(student.reg_no) ? 'btn-primary' : 'btn-outline'}`}
                              type="button"
                              onClick={() => onSaveRowMarks(student.reg_no)}
                              disabled={!isTestDetailRowDirty(student.reg_no)}
                            >
                              <i className="fas fa-save"></i>
                            </button>
                          </td>
                        ) : null}
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          )) : (
            <div className="table-wrapper report-marks-scroll">
              <table className="report-marks-table">
                <tbody>
                  <tr>
                    <td colSpan={testDetail.subjects.length + (testMarksReadOnly ? 4 : 5)} className="text-center text-muted" style={{ padding: 22 }}>
                      No students match the current search and sort filters.
                    </td>
                  </tr>
                </tbody>
              </table>
            </div>
          )}
        </div>
      </div>
    );
  }

  if (currentUser.role === 'counselor') {
    return (
      <div data-tour-id="counselor-reports">
        <h3 className="section-title"><i className="fas fa-file-lines"></i> Reports</h3>
        <CounselorTestsTable
          title="Semester 1"
          tests={counselorTestsBySemester.sem1}
          counselorTestsLoading={counselorTestsLoading}
          currentUser={currentUser}
          formatYearLevel={formatYearLevel}
          onLoadTestDetail={onLoadTestDetail}
          onStartCounselorSendFlow={onStartCounselorSendFlow}
          sendResultOpeningId={sendResultOpeningId}
        />
        <CounselorTestsTable
          title="Semester 2"
          tests={counselorTestsBySemester.sem2}
          counselorTestsLoading={counselorTestsLoading}
          currentUser={currentUser}
          formatYearLevel={formatYearLevel}
          onLoadTestDetail={onLoadTestDetail}
          onStartCounselorSendFlow={onStartCounselorSendFlow}
          sendResultOpeningId={sendResultOpeningId}
        />
      </div>
    );
  }

  if (reportsData?.showDepartmentPicker) {
    return (
      <div className="mb-3" data-tour-id="reports-workspace">
        <h3 className="section-title"><i className="fas fa-building"></i> Select Department</h3>
        <div className="metrics-grid selection-grid department-selection-grid">
          {(reportsData?.departments || []).map((department) => (
            <button
              key={department.id}
              type="button"
              className="metric-card selection-card-button"
              onClick={() => onLoadReports(department.code)}
            >
              <div className="metric-value" style={{ fontSize: '1.6rem' }}>{department.code}</div>
              <div className="selection-card-subtitle">{department.name}</div>
            </button>
          ))}
          {!reportsLoading && !(reportsData?.departments || []).length ? (
            <div className="card" style={{ padding: 16, fontSize: '.9rem', color: 'var(--text-dim)' }}>No departments available for your scope.</div>
          ) : null}
        </div>
      </div>
    );
  }

  if (reportsData?.showYearPicker) {
    return (
      <div
        key={`reports-year-picker-${reportsData.selectedDepartment || 'scope'}`}
        className="selection-shell selection-shell-stage-enter mb-3"
        data-tour-id="reports-workspace"
        style={{ maxWidth: 620 }}
      >
        <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 14 }}>
          <ScopeBreadcrumb
            icon="fa-file-lines"
            items={[
              { label: 'Reports', onClick: () => onLoadReports() },
              { label: reportsData.selectedDepartment },
            ]}
          />
        </div>
        <div className="selection-actions-grid">
          {reportsData.availableYears.map((year) => (
            <button
              key={year}
              type="button"
              className="btn btn-outline selection-action-button"
              onClick={() => onLoadReports(reportsData.selectedDepartment, year)}
            >
              {formatYearLevel(year)}
            </button>
          ))}
          {!reportsData.availableYears.length ? (
            <div className="card" style={{ padding: 12, fontSize: '.86rem', color: 'var(--text-dim)' }}>No years allocated for this department.</div>
          ) : null}
        </div>
      </div>
    );
  }

  if (reportsData?.selectedDepartment && reportsData?.selectedYear) {
    return (
      <div data-tour-id="reports-workspace">
        <div className="d-flex align-center justify-between flex-wrap mb-2" style={{ gap: 12 }}>
          <ScopeBreadcrumb
            icon="fa-file-lines"
            items={[
              { label: 'Reports', onClick: () => onLoadReports() },
              { label: reportsData.selectedDepartment, onClick: () => onLoadReports(reportsData.selectedDepartment) },
              { label: formatYearLevel(reportsData.selectedYear) },
            ]}
          />
        </div>

        {(currentUser.role === 'admin' || currentUser.role === 'deo') ? (
          <div className="card mb-3">
            <div className="card-title"><i className="fas fa-file-upload"></i> Upload Marksheet</div>
            <form onSubmit={onUploadReportSubmit}>
              <div className="form-row">
                <div className="form-group">
                  <label className="form-label">Department</label>
                  <input className="form-control" name="department" value={reportsData.selectedDepartment} readOnly />
                </div>
                <div className="form-group">
                  <label className="form-label">Year</label>
                  <input type="hidden" name="year_level" value={String(reportsData.selectedYear)} />
                  <input className="form-control" value={formatYearLevel(reportsData.selectedYear)} readOnly />
                </div>
              </div>
              <div className="form-row">
                <div className="form-group">
                  <label className="form-label">Test Name</label>
                  <div className="form-select-shell">
                    <i className="fas fa-file-lines select-shell-icon"></i>
                    <select
                      name="test_name"
                      className="form-control form-select-themed"
                      value={reportUploadDraft.test_name}
                      onChange={(event) => onReportUploadDraftChange('test_name', event.target.value)}
                      required
                    >
                      <option value="">-- Select Test --</option>
                      <option value="IAT 1">IAT 1</option>
                      <option value="IAT 2">IAT 2</option>
                      <option value="MODEL EXAM">MODEL EXAM</option>
                    </select>
                  </div>
                </div>
                <div className="form-group">
                  <label className="form-label">Semester</label>
                  <div className="form-select-shell">
                    <i className="fas fa-layer-group select-shell-icon"></i>
                    <select
                      name="semester"
                      className="form-control form-select-themed"
                      value={reportUploadDraft.semester}
                      onChange={(event) => onReportUploadDraftChange('semester', event.target.value)}
                      required
                    >
                      <option value="1">1</option>
                      <option value="2">2</option>
                    </select>
                  </div>
                </div>
              </div>
              <div className="form-group" style={{ maxWidth: 380 }}>
                <label className="form-label">Upload Mode</label>
                <input type="hidden" name="batch_name" value={reportUploadDraft.batch_name || getDefaultBatchNameForYearLevel(reportsData.selectedYear, appConfig)} />
                <input type="hidden" name="section" value={reportUploadDraft.section || ''} />
                <div className="form-select-shell">
                  <i className="fas fa-arrows-rotate select-shell-icon"></i>
                  <select
                    name="upload_mode"
                    className="form-control form-select-themed"
                    value={reportUploadDraft.upload_mode}
                    onChange={(event) => onReportUploadDraftChange('upload_mode', event.target.value)}
                  >
                    <option value="new">Keep as New Test</option>
                    <option value="replace">Replace Existing Matching Test</option>
                  </select>
                </div>
              </div>
              <div className="form-group">
                <label className="form-label">Marksheet File</label>
                <div className="file-input-wrapper">
                  <i className="fas fa-file-excel"></i>
                  <div className="file-text">Upload Excel marksheet (.xlsx, .xls)</div>
                  <div className="file-name" style={{ display: reportUploadDraft.file ? 'block' : 'none' }}>{reportUploadDraft.file?.name || ''}</div>
                  <input
                    key={reportUploadInputKey}
                    type="file"
                    name="marks_file"
                    accept=".xlsx,.xls"
                    onChange={(event) => onReportUploadFileChange(event.target.files?.[0] || null)}
                    required
                  />
                </div>
              </div>
              <button className="btn btn-primary" type="submit" disabled={uploadingReport}>
                <i className={`fas ${uploadingReport ? 'fa-spinner fa-spin' : 'fa-upload'}`}></i> {uploadingReport ? 'Uploading...' : 'Upload Marksheet'}
              </button>
            </form>
          </div>
        ) : null}

        <ReportTestsTable
          title={`${reportsData.selectedDepartment} - ${formatYearLevel(reportsData.selectedYear)} - Semester 1`}
          tests={reportTestsBySemester.sem1}
          reportsLoading={reportsLoading}
          currentUser={currentUser}
          formatUploadDateTime={formatUploadDateTime}
          onLoadTestDetail={onLoadTestDetail}
          onToggleTestBlock={onToggleTestBlock}
          onDeleteTest={onDeleteTest}
        />
        <ReportTestsTable
          title={`${reportsData.selectedDepartment} - ${formatYearLevel(reportsData.selectedYear)} - Semester 2`}
          tests={reportTestsBySemester.sem2}
          reportsLoading={reportsLoading}
          currentUser={currentUser}
          formatUploadDateTime={formatUploadDateTime}
          onLoadTestDetail={onLoadTestDetail}
          onToggleTestBlock={onToggleTestBlock}
          onDeleteTest={onDeleteTest}
        />
      </div>
    );
  }

  return null;
}

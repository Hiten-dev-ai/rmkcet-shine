import { useMemo } from 'react';
import type { ChangeEvent, FormEvent } from 'react';
import { VirtualizedRowsTable } from '../components/VirtualizedRowsTable';
import type { BootstrapMetrics, DepartmentRecord, Role, UserRecord } from '../types';

type UserCreateFormState = {
  name: string;
  email: string;
  password: string;
  confirm_password: string;
  role: Role;
  designation: string;
  department: string;
  year_level: string;
  max_students: string;
  scope_pairs: string[];
};

type BulkCounselorFormState = {
  year_level: string;
  file: File | null;
};

type UserActionKind = 'lock' | 'unlock' | 'delete';

type GroupedUserDisplayRow = {
  email: string;
  name: string;
  roles: UserRecord[];
};

type UsersTabProps = {
  currentUserRole: Role;
  metrics: BootstrapMetrics | null;
  filteredUsers: UserRecord[];
  usersLoading: boolean;
  userSearch: string;
  onUserSearchChange: (value: string) => void;
  userFilterTrayOpen: boolean;
  onToggleFilterTray: () => void;
  onRefreshUsers: () => void;
  userSortBy: string;
  onUserSortChange: (value: string) => void;
  userFilterDepartment: string;
  onUserFilterDepartmentChange: (value: string) => void;
  userFilterRole: string;
  onUserFilterRoleChange: (value: string) => void;
  userFilterStatus: string;
  onUserFilterStatusChange: (value: string) => void;
  userFilterYear: string;
  onUserFilterYearChange: (value: string) => void;
  userFilterStudentList: string;
  onUserFilterStudentListChange: (value: string) => void;
  onResetUserFilters: () => void;
  userSelectableDepartments: DepartmentRecord[];
  userScopeOptions: Array<{ department: string; year_level: number }>;
  getRoleBadgeClass: (role: Role) => string;
  getRoleOptionLabel: (role: Role, designation?: string | null) => string;
  formatYearLevel: (year: number) => string;
  onOpenEditUserModal: (user: UserRecord) => void;
  onSetUserActionTarget: (kind: UserActionKind, user: UserRecord) => void;
  onManageLinkedUsers: (email: string) => void;
  userAssignableRoles: Role[];
  userCreateForm: UserCreateFormState;
  userCreateEmailExists: boolean;
  userCreateEmailDomainValid: boolean;
  userCreateAvailableRoles: Role[];
  userCreateExistingName: string;
  managedUserDomain: string;
  onUserCreateFieldChange: (field: 'name' | 'email' | 'password' | 'confirm_password' | 'designation' | 'department' | 'year_level' | 'max_students', value: string) => void;
  onUserCreateRoleChange: (role: Role) => void;
  onToggleUserCreateScopePair: (value: string, checked: boolean) => void;
  onCreateUserSubmit: (event: FormEvent<HTMLFormElement>) => void;
  onClearUserCreateForm: () => void;
  userSaving: boolean;
  bulkCounselorForm: BulkCounselorFormState;
  bulkCounselorUploadKey: number;
  onBulkCounselorYearChange: (value: string) => void;
  onBulkCounselorFileChange: (file: File | null) => void;
  onBulkCounselorUploadSubmit: (event: FormEvent<HTMLFormElement>) => void;
  bulkCounselorSaving: boolean;
  googleOauthEnabled: boolean;
};

export default function UsersTab({
  currentUserRole,
  metrics,
  filteredUsers,
  usersLoading,
  userSearch,
  onUserSearchChange,
  userFilterTrayOpen,
  onToggleFilterTray,
  onRefreshUsers,
  userSortBy,
  onUserSortChange,
  userFilterDepartment,
  onUserFilterDepartmentChange,
  userFilterRole,
  onUserFilterRoleChange,
  userFilterStatus,
  onUserFilterStatusChange,
  userFilterYear,
  onUserFilterYearChange,
  userFilterStudentList,
  onUserFilterStudentListChange,
  onResetUserFilters,
  userSelectableDepartments,
  userScopeOptions,
  getRoleBadgeClass,
  getRoleOptionLabel,
  formatYearLevel,
  onOpenEditUserModal,
  onSetUserActionTarget,
  onManageLinkedUsers,
  userAssignableRoles,
  userCreateForm,
  userCreateEmailExists,
  userCreateEmailDomainValid,
  userCreateAvailableRoles,
  userCreateExistingName,
  managedUserDomain,
  onUserCreateFieldChange,
  onUserCreateRoleChange,
  onToggleUserCreateScopePair,
  onCreateUserSubmit,
  onClearUserCreateForm,
  userSaving,
  bulkCounselorForm,
  bulkCounselorUploadKey,
  onBulkCounselorYearChange,
  onBulkCounselorFileChange,
  onBulkCounselorUploadSubmit,
  bulkCounselorSaving,
  googleOauthEnabled,
}: UsersTabProps) {
  const groupedUsers = useMemo(() => {
    const groups = new Map<string, GroupedUserDisplayRow>();
    for (const row of filteredUsers) {
      const key = String(row.email || '').trim().toLowerCase();
      const existing = groups.get(key);
      if (existing) {
        existing.roles.push(row);
        continue;
      }
      groups.set(key, {
        email: row.email,
        name: row.name,
        roles: [row],
      });
    }
    return Array.from(groups.values());
  }, [filteredUsers]);

  return (
    <div data-tour-id="users-workspace">
      <div className="metrics-grid mb-3">
        <div className="metric-card">
          <div className="metric-label">Total Users</div>
          <div className="metric-value">{metrics?.totalUsers ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-users"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Counselors</div>
          <div className="metric-value">{metrics?.counselorCount ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-chalkboard-teacher"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Active Sessions</div>
          <div className="metric-value">{metrics?.activeSessions ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-signal"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Messages Sent</div>
          <div className="metric-value">{metrics?.messagesSent ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-paper-plane"></i></div>
        </div>
      </div>

      <div className="card mb-3">
        <h3 className="section-title"><i className="fas fa-list"></i> User List ({groupedUsers.length})</h3>
        <div className="global-action-bar">
          <div className="form-group" style={{ flex: 1, minWidth: 260 }}>
            <label className="form-label">Search by Name</label>
            <input
              className="form-control"
              type="text"
              placeholder="Type name to search..."
              value={userSearch}
              onChange={(event) => onUserSearchChange(event.target.value)}
            />
          </div>
          <div className="form-group" style={{ minWidth: 120, alignSelf: 'end' }}>
            <button type="button" className="btn btn-outline btn-sm" onClick={onToggleFilterTray}>
              <i className="fas fa-filter"></i> Filters
            </button>
          </div>
          <div className="form-group" style={{ minWidth: 120, alignSelf: 'end' }}>
            <button type="button" className="btn btn-outline btn-sm" onClick={onRefreshUsers}>
              <i className="fas fa-rotate"></i> Refresh
            </button>
          </div>
        </div>

        {userFilterTrayOpen ? (
          <div className="filter-tray" style={{ marginBottom: 14 }}>
            <select className="form-control" value={userSortBy} onChange={(event) => onUserSortChange(event.target.value)} style={{ maxWidth: 180 }}>
              <option value="name_asc">Name A-Z</option>
              <option value="name_desc">Name Z-A</option>
              <option value="date_added">Date Added</option>
              <option value="role">Role</option>
              <option value="department">Department</option>
              <option value="year">Year</option>
            </select>
            <select className="form-control" value={userFilterDepartment} onChange={(event) => onUserFilterDepartmentChange(event.target.value)} style={{ maxWidth: 180 }}>
              <option value="">All Departments</option>
              {userSelectableDepartments.map((department) => (
                <option key={department.id} value={department.code}>{department.code}</option>
              ))}
            </select>
            <select className="form-control" value={userFilterRole} onChange={(event) => onUserFilterRoleChange(event.target.value)} style={{ maxWidth: 170 }}>
              <option value="">All Account Types</option>
              <option value="admin">System Admin</option>
              <option value="principal">Higher Official</option>
              <option value="hod">HoD</option>
              <option value="deo">DEO</option>
              <option value="counselor">Counselor</option>
            </select>
            <select className="form-control" value={userFilterStatus} onChange={(event) => onUserFilterStatusChange(event.target.value)} style={{ maxWidth: 150 }}>
              <option value="">All States</option>
              <option value="active">Active</option>
              <option value="inactive">Inactive</option>
            </select>
            <select className="form-control" value={userFilterYear} onChange={(event) => onUserFilterYearChange(event.target.value)} style={{ maxWidth: 140 }}>
              <option value="">All Years</option>
              <option value="1">Year 1</option>
              <option value="2">Year 2</option>
              <option value="3">Year 3</option>
              <option value="4">Year 4</option>
            </select>
            <select className="form-control" value={userFilterStudentList} onChange={(event) => onUserFilterStudentListChange(event.target.value)} style={{ maxWidth: 220 }}>
              <option value="">All Student List Status</option>
              <option value="with_students">Counselors With Student List</option>
              <option value="no_students">Counselors With No Student List</option>
            </select>
            <button type="button" className="btn btn-outline btn-sm" onClick={onResetUserFilters}>
              <i className="fas fa-rotate-left"></i> Reset
            </button>
          </div>
        ) : null}

        {usersLoading && !groupedUsers.length ? (
          <div className="panel-placeholder">Loading users...</div>
        ) : (
          <VirtualizedRowsTable
            columns={[
              {
                key: 'name',
                label: 'Name',
                width: '2.2fr',
                className: 'virtualized-table-cell-stack',
                render: (row: GroupedUserDisplayRow) => (
                  <div className="virtualized-counselor-cell">
                    <strong>{row.name}</strong>
                    <span className="inline-muted virtualized-email-text">{row.email}</span>
                  </div>
                ),
              },
              {
                key: 'role',
                label: 'Role',
                width: '1.4fr',
                render: (row: GroupedUserDisplayRow) => (
                  <div className="btn-group" style={{ gap: 6, flexWrap: 'wrap' }}>
                    {row.roles.map((entry) => (
                      <span key={entry.account_email || `${row.email}:${entry.role}`} className={`badge ${getRoleBadgeClass(entry.role)}`}>
                        {getRoleOptionLabel(entry.role, entry.designation)}
                      </span>
                    ))}
                  </div>
                ),
              },
              {
                key: 'department',
                label: 'Department',
                width: '1fr',
                render: (row: GroupedUserDisplayRow) => {
                  const departments = Array.from(new Set(row.roles.flatMap((entry) => (
                    entry.role === 'hod' || entry.role === 'deo'
                      ? ((entry.scopes || []).map((scope) => scope.department).filter(Boolean))
                      : [entry.department || '']
                  )).filter(Boolean)));
                  if (!departments.length) return '-';
                  return departments.length <= 2 ? departments.join(', ') : 'Multiple';
                },
              },
              {
                key: 'year',
                label: 'Year',
                width: '0.8fr',
                render: (row: GroupedUserDisplayRow) => {
                  const years = Array.from(new Set(row.roles.filter((entry) => entry.role === 'counselor').map((entry) => Number(entry.year_level || 0)).filter((value) => value > 0)));
                  if (!years.length) return '-';
                  return years.length === 1 ? formatYearLevel(years[0]) : 'Multiple';
                },
              },
              {
                key: 'status',
                label: 'Status',
                width: '0.9fr',
                render: (row: GroupedUserDisplayRow) => {
                  const activeCount = row.roles.filter((entry) => entry.is_active && !entry.is_locked).length;
                  if (activeCount === row.roles.length) return <span className="badge badge-success">Active</span>;
                  if (!activeCount) return <span className="badge badge-danger">Inactive</span>;
                  return <span className="badge badge-info">Mixed</span>;
                },
              },
              {
                key: 'actions',
                label: 'Actions',
                width: '1.5fr',
                render: (row: GroupedUserDisplayRow) => {
                  if (row.roles.length > 1) {
                    return (
                      <button type="button" className="btn btn-outline btn-sm" onClick={() => onManageLinkedUsers(row.email)}>
                        <i className="fas fa-layer-group"></i> Manage Roles
                      </button>
                    );
                  }
                  const account = row.roles[0];
                  return (
                    <div className="btn-group">
                      {account.can_edit ? (
                        <button type="button" className="btn btn-outline btn-sm" onClick={() => onOpenEditUserModal(account)}>
                          <i className="fas fa-edit"></i> Edit
                        </button>
                      ) : null}
                      {account.can_manage ? (
                        <>
                          <button
                            type="button"
                            className={`btn btn-sm ${account.is_locked ? 'btn-success' : 'btn-warning'}`}
                            onClick={() => onSetUserActionTarget(account.is_locked ? 'unlock' : 'lock', account)}
                          >
                            <i className={`fas fa-${account.is_locked ? 'unlock' : 'lock'}`}></i>
                          </button>
                          <button type="button" className="btn btn-danger btn-sm" onClick={() => onSetUserActionTarget('delete', account)}>
                            <i className="fas fa-trash"></i>
                          </button>
                        </>
                      ) : (
                        <span className="badge badge-info">View Only</span>
                      )}
                    </div>
                  );
                },
              },
            ]}
            rows={groupedUsers}
            rowKey={(row) => row.email}
            rowHeight={72}
            maxHeight={640}
            emptyMessage="No users matched the current filter."
          />
        )}
      </div>

      {currentUserRole !== 'principal' ? (
        <div className="card mb-3">
          <div className="d-flex justify-between align-center flex-wrap" style={{ gap: 12, marginBottom: 12 }}>
            <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-user-plus"></i> Register New User</div>
            <button type="button" className="btn btn-outline btn-sm" onClick={onClearUserCreateForm}>
              <i className="fas fa-eraser"></i> Clear
            </button>
          </div>
          <form onSubmit={(event) => void onCreateUserSubmit(event)} autoComplete="off">
            <div className="form-row">
              <div className="form-group">
                <label className="form-label">Full Name</label>
                <input className="form-control" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.name} onChange={(event) => onUserCreateFieldChange('name', event.target.value)} required placeholder="Dr. John Doe" disabled={userCreateEmailExists} />
              </div>
              <div className="form-group">
                <label className="form-label">Email</label>
                <input className="form-control" type="email" autoComplete="off" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.email} onChange={(event) => onUserCreateFieldChange('email', event.target.value)} required placeholder="john@rmkcet.ac.in" />
                {!userCreateEmailDomainValid ? (
                  <small style={{ color: 'var(--danger)', fontSize: '.75rem', marginTop: 4, display: 'block' }}>
                    Only `{managedUserDomain}` addresses are allowed.
                  </small>
                ) : userCreateEmailExists ? (
                  <small style={{ color: 'var(--text-dim)', fontSize: '.75rem', marginTop: 4, display: 'block' }}>
                    Email already exists for {userCreateExistingName || 'this account'}. Please select another role.
                  </small>
                ) : null}
              </div>
            </div>
            <div className="form-row">
              <div className="form-group">
                <label className="form-label">Password</label>
                <input className="form-control" type="password" autoComplete="new-password" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.password} onChange={(event) => onUserCreateFieldChange('password', event.target.value)} required={!userCreateEmailExists} disabled={userCreateEmailExists} placeholder={userCreateEmailExists ? 'Reuses the existing email password' : 'Minimum 6 characters'} />
              </div>
              <div className="form-group">
                <label className="form-label">Confirm Password</label>
                <input className="form-control" type="password" autoComplete="new-password" data-lpignore="true" data-1p-ignore="true" value={userCreateForm.confirm_password} onChange={(event) => onUserCreateFieldChange('confirm_password', event.target.value)} required={!userCreateEmailExists} disabled={userCreateEmailExists} placeholder={userCreateEmailExists ? 'No new password needed' : 'Re-enter password'} />
              </div>
            </div>
            {currentUserRole === 'admin' ? (
              <div className="form-row">
                <div className="form-group">
                  <label className="form-label">Role</label>
                  <select className="form-control" value={userCreateForm.role} onChange={(event) => onUserCreateRoleChange(event.target.value as Role)}>
                    {userCreateAvailableRoles.map((role) => (
                      <option key={role} value={role}>{getRoleOptionLabel(role)}</option>
                    ))}
                  </select>
                  {userCreateEmailExists && !userCreateAvailableRoles.length ? (
                    <small style={{ color: 'var(--danger)', fontSize: '.75rem', marginTop: 4, display: 'block' }}>
                      All roles are already assigned for this email.
                    </small>
                  ) : null}
                </div>
              </div>
            ) : null}
            {userCreateForm.role === 'principal' ? (
              <div className="form-row">
                <div className="form-group">
                  <label className="form-label">Higher Official Designation</label>
                  <input
                    className="form-control"
                    autoComplete="off"
                    value={userCreateForm.designation}
                    onChange={(event) => onUserCreateFieldChange('designation', event.target.value)}
                    placeholder="Vice Chairman, Dean, Director..."
                  />
                </div>
              </div>
            ) : null}
            {(userCreateForm.role === 'hod' || userCreateForm.role === 'deo') ? (
              <div className="card mb-2" style={{ padding: 12, background: 'rgba(59,130,246,.08)', border: '1px solid rgba(59,130,246,.28)' }}>
                <div className="card-title" style={{ fontSize: '.86rem', marginBottom: 10 }}><i className="fas fa-layer-group"></i> Assigned Scopes</div>
                <div className="scope-grid">
                  {userSelectableDepartments.map((department) => (
                    <div key={department.id} className="scope-item">
                      <div className="scope-item-title">{department.code}</div>
                      <div className="scope-year-list">
                        {(currentUserRole === 'admin' ? [1, 2, 3, 4] : userScopeOptions.filter((scope) => scope.department === department.code).map((scope) => scope.year_level)).map((year) => {
                          const value = `${department.code}::${year}`;
                          return (
                            <label key={value} className="scope-chip">
                              <input
                                type="checkbox"
                                checked={userCreateForm.scope_pairs.includes(value)}
                                onChange={(event) => onToggleUserCreateScopePair(value, event.target.checked)}
                              />
                              <span>Y{year}</span>
                            </label>
                          );
                        })}
                      </div>
                    </div>
                  ))}
                </div>
              </div>
            ) : null}
            {userCreateForm.role === 'counselor' ? (
              <>
                <div className="form-row">
                  <div className="form-group">
                    <label className="form-label">Department</label>
                    <select className="form-control" value={userCreateForm.department} onChange={(event) => onUserCreateFieldChange('department', event.target.value)} required>
                      <option value="">-- Select --</option>
                      {userSelectableDepartments.map((department) => (
                        <option key={department.id} value={department.code}>{department.code} - {department.name}</option>
                      ))}
                    </select>
                  </div>
                  <div className="form-group">
                    <label className="form-label">Year</label>
                    <select className="form-control" value={userCreateForm.year_level} onChange={(event) => onUserCreateFieldChange('year_level', event.target.value)}>
                      {[1, 2, 3, 4].map((year) => (
                        <option key={year} value={year}>{formatYearLevel(year)}</option>
                      ))}
                    </select>
                  </div>
                </div>
                <div className="form-group" style={{ maxWidth: 220 }}>
                  <label className="form-label">Max Students</label>
                  <input className="form-control" type="number" min="1" max="500" value={userCreateForm.max_students} onChange={(event) => onUserCreateFieldChange('max_students', event.target.value)} />
                </div>
              </>
            ) : null}
            <button type="submit" className="btn btn-primary" disabled={userSaving || !userCreateEmailDomainValid || (userCreateEmailExists && !userCreateAvailableRoles.length)}>
              <i className={`fas ${userSaving ? 'fa-spinner fa-spin' : 'fa-user-plus'}`}></i> Create User
            </button>
          </form>
        </div>
      ) : null}

      {currentUserRole !== 'principal' ? (
        <div className="card">
          <div className="card-title"><i className="fas fa-upload"></i> Bulk Counselor Upload</div>
          <form onSubmit={(event) => void onBulkCounselorUploadSubmit(event)}>
            <div className="form-row">
              <div className="form-group" style={{ maxWidth: 220 }}>
                <label className="form-label">Year</label>
                <select className="form-control" value={bulkCounselorForm.year_level} onChange={(event) => onBulkCounselorYearChange(event.target.value)}>
                  {[1, 2, 3, 4].map((year) => (
                    <option key={year} value={year}>{formatYearLevel(year)}</option>
                  ))}
                </select>
              </div>
            </div>
            <div className="form-group">
              <label className="form-label">Counselor Excel File</label>
              <div className="file-input-wrapper">
                <i className="fas fa-file-excel"></i>
                <div className="file-text">Choose file</div>
                <div className="file-name" style={{ display: bulkCounselorForm.file ? 'block' : 'none' }}>{bulkCounselorForm.file?.name || ''}</div>
                <input
                  key={bulkCounselorUploadKey}
                  type="file"
                  accept=".xlsx,.xls"
                  onChange={(event: ChangeEvent<HTMLInputElement>) => onBulkCounselorFileChange(event.target.files?.[0] || null)}
                  required
                />
              </div>
            </div>
            <div className="card" style={{ padding: 12, background: 'rgba(59,130,246,.08)', border: '1px solid rgba(59,130,246,.22)', marginBottom: 12 }}>
              <div style={{ fontSize: '.84rem', color: 'var(--text-dim)' }}>
                {googleOauthEnabled
                  ? 'Google OAuth is enabled. Bulk-uploaded counselor passwords follow the configured sheet/override policy from settings.'
                  : 'Google OAuth is disabled. Bulk-uploaded counselor passwords use the configured non-OAuth fallback from settings, or the password from the sheet when no override is configured.'}
              </div>
            </div>
            <button type="submit" className="btn btn-primary" disabled={bulkCounselorSaving}>
              <i className={`fas ${bulkCounselorSaving ? 'fa-spinner fa-spin' : 'fa-upload'}`}></i> Run Bulk Upload
            </button>
          </form>
        </div>
      ) : null}
    </div>
  );
}

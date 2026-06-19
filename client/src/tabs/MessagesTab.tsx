import { useMemo } from 'react';
import type { ComponentType } from 'react';
import type { AdminMessagesOverviewPayload } from '../types';

type SmartDateInputProps = {
  value: string;
  onChange: (nextValue: string) => void;
  placeholder?: string;
  id?: string;
};

type MessageFilters = {
  day: string;
  q: string;
  year: string;
  month: string;
  day_num: string;
};

type MessagesTabProps = {
  adminMessagesLoading: boolean;
  adminMessagesData: AdminMessagesOverviewPayload | null;
  adminMessageFilters: MessageFilters;
  adminMessageSearch: string;
  selectedAdminMessageIds: number[];
  SmartDateInput: ComponentType<SmartDateInputProps>;
  onReloadAdminMessages: (filters?: MessageFilters) => void;
  onAdminMessageDayChange: (nextValue: string) => void;
  onAdminMessageSearchChange: (nextValue: string) => void;
  onResetAdminMessageFilters: () => void;
  onPickAdminMessageDay: (day: string) => void;
  onToggleSelectAll: (checked: boolean) => void;
  onToggleSelectMessage: (id: number, checked: boolean) => void;
  onDeleteSelected: () => void;
  onDeleteMessage: (id: number) => void;
  onLoadMore: () => void;
};

export default function MessagesTab({
  adminMessagesLoading,
  adminMessagesData,
  adminMessageFilters,
  adminMessageSearch,
  selectedAdminMessageIds,
  SmartDateInput,
  onReloadAdminMessages,
  onAdminMessageDayChange,
  onAdminMessageSearchChange,
  onResetAdminMessageFilters,
  onPickAdminMessageDay,
  onToggleSelectAll,
  onToggleSelectMessage,
  onDeleteSelected,
  onDeleteMessage,
  onLoadMore,
}: MessagesTabProps) {
  const selectedAdminMessageIdSet = useMemo(() => new Set(selectedAdminMessageIds), [selectedAdminMessageIds]);

  return (
    <div className="messages-tab-surface" data-tour-id="messages-workspace">
      <div className="metrics-grid mb-3">
        <div className="metric-card">
          <div className="metric-label">Total Messages</div>
          <div className="metric-value">{adminMessagesData?.stats.total ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-envelope"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Today</div>
          <div className="metric-value">{adminMessagesData?.stats.today ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-calendar-day"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Active Counselors</div>
          <div className="metric-value">{adminMessagesData?.stats.active_counselors ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-user-group"></i></div>
        </div>
        <div className="metric-card">
          <div className="metric-label">Visible Days</div>
          <div className="metric-value">{adminMessagesData?.messageDays.length ?? 0}</div>
          <div className="metric-icon"><i className="fas fa-calendar-alt"></i></div>
        </div>
      </div>

      <div className="card mb-3">
        <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
          <div className="card-title" style={{ marginBottom: 0 }}><i className="fas fa-envelope-open-text"></i> Message Logs</div>
          <button type="button" className="btn btn-outline btn-sm" disabled={adminMessagesLoading} onClick={() => onReloadAdminMessages(adminMessageFilters)}>
            <i className={`fas ${adminMessagesLoading ? 'fa-spinner fa-spin' : 'fa-rotate'}`}></i> Refresh
          </button>
        </div>
        <div>
          <div className="form-row">
            <div className="form-group">
              <label className="form-label">Date</label>
              <SmartDateInput value={adminMessageFilters.day} onChange={onAdminMessageDayChange} />
            </div>
            <div className="form-group" style={{ minWidth: 240 }}>
              <label className="form-label">Search Counselor</label>
              <input
                className="form-control"
                autoComplete="off"
                data-lpignore="true"
                data-1p-ignore="true"
                value={adminMessageSearch}
                onChange={(event) => onAdminMessageSearchChange(event.target.value)}
                placeholder="Type counselor name or email"
              />
            </div>
          </div>
          <div className="btn-group">
            <button type="button" className="btn btn-outline btn-sm" onClick={onResetAdminMessageFilters}>
              <i className="fas fa-rotate-left"></i> Reset
            </button>
          </div>
        </div>
      </div>

      <div className="card">
        <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 12 }}>
          <label className="form-check" style={{ margin: 0 }}>
            <input
              type="checkbox"
              checked={!!adminMessagesData?.messages.length && selectedAdminMessageIds.length === adminMessagesData.messages.length}
              disabled={adminMessagesLoading && !adminMessagesData}
              onChange={(event) => onToggleSelectAll(event.target.checked)}
            />
            <span>Select all on current view</span>
          </label>
          <button type="button" className="btn btn-danger btn-sm" disabled={adminMessagesLoading && !adminMessagesData} onClick={onDeleteSelected}>
            <i className="fas fa-trash"></i> Delete Selected
          </button>
        </div>

        <div className="d-flex justify-between align-center flex-wrap mb-2" style={{ gap: 8 }}>
          <span className="inline-muted">
            Showing {adminMessagesData?.loadedCount ?? adminMessagesData?.messages.length ?? 0} message logs
            {adminMessagesData?.hasMore ? ' (more available)' : ''}
          </span>
          {adminMessagesLoading && adminMessagesData ? (
            <span className="badge badge-info">Updating...</span>
          ) : null}
        </div>

        {adminMessagesLoading && !adminMessagesData ? (
          <div className="panel-placeholder">Loading message logs...</div>
        ) : (adminMessagesData?.groups || []).length ? (
          adminMessagesData!.groups.map((group) => (
            <div key={group.day} className="card mb-2" style={{ padding: 12 }}>
              <div className="d-flex justify-between align-center mb-1" style={{ gap: 8 }}>
                <strong>Day: {group.day}</strong>
                <span className="badge badge-info">{group.total} messages</span>
              </div>
              <div className="table-wrapper table-scroll-lg">
                <table className="sticky-table">
                  <thead>
                    <tr>
                      <th style={{ width: 34 }}></th>
                      <th>Time</th>
                      <th>Counselor</th>
                      <th>Student</th>
                      <th>Reg No</th>
                      <th>Mode</th>
                      <th>Status</th>
                      <th>Action</th>
                    </tr>
                  </thead>
                  <tbody>
                    {group.messages.map((message) => (
                      <tr key={message.id}>
                        <td>
                          <input
                            type="checkbox"
                            checked={selectedAdminMessageIdSet.has(message.id)}
                            onChange={(event) => onToggleSelectMessage(message.id, event.target.checked)}
                          />
                        </td>
                        <td style={{ fontSize: '.82rem' }}>{String(message.sent_at || '').slice(11, 19) || '--'}</td>
                        <td>{message.counselor_name || message.counselor_email || '-'}</td>
                        <td>{message.student_name || '-'}</td>
                        <td><strong>{message.reg_no || '-'}</strong></td>
                        <td>
                          <span className={`badge ${String(message.send_mode || 'app').toLowerCase() === 'web' ? 'badge-info' : 'badge-primary'}`}>
                            {String(message.send_mode || 'app').toUpperCase()}
                          </span>
                        </td>
                        <td>
                          <span className={`badge ${String(message.status || '').toLowerCase() === 'sent' ? 'badge-success' : 'badge-warning'}`}>
                            {message.status || 'Pending'}
                          </span>
                        </td>
                        <td>
                          <button type="button" className="btn btn-danger btn-sm" onClick={() => onDeleteMessage(message.id)}>
                            <i className="fas fa-trash"></i>
                          </button>
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
              </div>
            </div>
          ))
        ) : (
          <div className="panel-placeholder">No message activity found for the selected filters.</div>
        )}

        {adminMessagesData?.hasMore ? (
          <div className="text-center" style={{ marginTop: 14 }}>
            <button type="button" className="btn btn-outline btn-sm" disabled={adminMessagesLoading} onClick={onLoadMore}>
              <i className={`fas ${adminMessagesLoading ? 'fa-spinner fa-spin' : 'fa-plus'}`}></i> Load More
            </button>
          </div>
        ) : null}
      </div>
    </div>
  );
}

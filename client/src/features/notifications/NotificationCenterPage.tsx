import { memo } from 'react';

export type NotificationCenterItem = {
  key: string;
  severity: 'info' | 'warning' | 'critical';
  title: string;
  body: string;
  createdAt: string;
  actionTab?: string;
};

type NotificationCenterPageProps = {
  notifications: NotificationCenterItem[];
  seenKeys: Set<string>;
  unreadCount: number;
  formatDateTime: (value: string) => string;
  onBack: () => void;
  onMarkRead: (keys: string[]) => void;
  onDelete: (keys: string[]) => void;
  onOpenTab: (tab: string) => void;
};

export const NotificationCenterPage = memo(function NotificationCenterPage({
  notifications,
  seenKeys,
  unreadCount,
  formatDateTime,
  onBack,
  onMarkRead,
  onDelete,
  onOpenTab,
}: NotificationCenterPageProps) {
  return (
    <section className="notification-page">
      <div className="card mb-3">
        <div className="notification-page-header">
          <button type="button" className="btn btn-outline btn-sm" onClick={onBack}>
            <i className="fas fa-arrow-left"></i> Back
          </button>
          <div>
            <div className="card-title" style={{ marginBottom: 2 }}><i className="fas fa-bell"></i> Notification Center</div>
            <div className="inline-muted">{unreadCount} unread notification{unreadCount === 1 ? '' : 's'}</div>
          </div>
          {notifications.length ? (
            <div className="notification-page-actions">
              <button type="button" className="btn btn-outline btn-sm" onClick={() => onMarkRead(notifications.map((item) => item.key))}>
                <i className="fas fa-check-double"></i> Mark All Read
              </button>
              <button type="button" className="btn btn-danger btn-sm" onClick={() => onDelete(notifications.map((item) => item.key))}>
                <i className="fas fa-trash"></i> Delete All
              </button>
            </div>
          ) : null}
        </div>
      </div>
      {notifications.length ? (
        <div className="notification-page-list">
          {notifications.map((item) => {
            const unread = !seenKeys.has(item.key);
            return (
              <article key={item.key} className={`notification-page-item ${unread ? 'unread' : ''} notification-${item.severity}`}>
                <button
                  type="button"
                  className="notification-page-main"
                  onClick={() => {
                    onMarkRead([item.key]);
                    if (item.actionTab) onOpenTab(item.actionTab);
                  }}
                >
                  <span className="notification-dot" aria-hidden="true"></span>
                  <span className="notification-content">
                    <strong>{item.title}</strong>
                    <span>{item.body}</span>
                    {item.createdAt ? <small>{formatDateTime(item.createdAt)}</small> : null}
                  </span>
                </button>
                <button type="button" className="btn btn-outline btn-sm" onClick={() => onDelete([item.key])}>
                  <i className="fas fa-trash"></i> Delete
                </button>
              </article>
            );
          })}
        </div>
      ) : (
        <div className="card"><div className="panel-placeholder">No notifications right now.</div></div>
      )}
    </section>
  );
});

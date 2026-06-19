import { memo } from 'react';

type CreditsPageProps = {
  compiledHtml: string;
  loading: boolean;
  error: string;
  onBack: () => void;
  onRefresh: () => void;
};

export const CreditsPage = memo(function CreditsPage({
  compiledHtml,
  loading,
  error,
  onBack,
  onRefresh,
}: CreditsPageProps) {
  return (
    <section className="credits-app-page">
      <div className="credits-page-hero credits-app-hero">
        <div>
          <p className="credits-page-kicker">Acknowledgements</p>
          <h1 className="credits-page-title">Project Credits</h1>
          <p className="credits-page-subtitle">The people behind RMKCET Shine, rendered inside the workspace.</p>
        </div>
        <div className="credits-app-actions">
          <button type="button" className="credits-back-btn" onClick={onBack}>
            <i className="fas fa-arrow-left"></i> Back
          </button>
          <button type="button" className="credits-back-btn" onClick={onRefresh} disabled={loading}>
            <i className={`fas ${loading ? 'fa-spinner fa-spin' : 'fa-rotate'}`}></i> Refresh
          </button>
        </div>
      </div>

      <div className="credits-page-body credits-app-body">
        {loading && !compiledHtml ? (
          <div className="panel-placeholder">Loading credits...</div>
        ) : error ? (
          <div className="credits-compiled-shell">
            <div className="credits-compiled-header">
              <h2 className="credits-compiled-title">Credits unavailable</h2>
              <p className="credits-compiled-subtitle">{error}</p>
            </div>
          </div>
        ) : compiledHtml ? (
          <div dangerouslySetInnerHTML={{ __html: compiledHtml }} />
        ) : (
          <div className="panel-placeholder">Credits will appear here.</div>
        )}
      </div>
    </section>
  );
});

import { useEffect, useMemo, useState } from 'react';
import type { AppConfig, AuthUser, Role } from '../../types';

export type TutorialStep = {
  id: string;
  tab?: string;
  targetId: string;
  title: string;
  body: string;
  actionHint?: string;
  allowClickThrough?: boolean;
  waitForTarget?: number;
  continueWhenTargetId?: string;
  clickToAdvance?: boolean;
  clickHint?: string;
  preventTargetAction?: boolean;
};

export type TutorialState = {
  open: boolean;
  role: Role;
  stepIndex: number;
  skippedStepIds: string[];
  completedAt?: string;
};

type TutorialProgress = {
  stepIndex: number;
  completedAt?: string;
};

type SupportGuideLauncherProps = {
  open: boolean;
  user: AuthUser;
  appConfig: AppConfig | null;
  activeTab: string;
  navTabs: string[];
  onClose: () => void;
  onNavigateTab: (tab: string) => void;
};

type TargetRect = {
  top: number;
  left: number;
  width: number;
  height: number;
};

function isTruthyConfig(value: unknown, fallback = true) {
  if (value === undefined || value === null || value === '') return fallback;
  return String(value).trim().toLowerCase() === 'true';
}

function getTutorialRole(user: AuthUser): Role | null {
  if (user.role === 'counselor' || user.role === 'hod' || user.role === 'principal') return user.role;
  return null;
}

function getRoleName(role: Role | null) {
  if (role === 'counselor') return 'Counsellor';
  if (role === 'hod') return 'HoD';
  if (role === 'principal') return 'Higher Official';
  return 'Unsupported';
}

function isTutorialEnabledForRole(role: Role | null, appConfig: AppConfig | null) {
  if (!role) return false;
  if (!isTruthyConfig(appConfig?.tutorial_master_enabled, true)) return false;
  if (role === 'counselor') return isTruthyConfig(appConfig?.tutorial_counselor_enabled, true);
  if (role === 'hod') return isTruthyConfig(appConfig?.tutorial_hod_enabled, true);
  if (role === 'principal') return isTruthyConfig(appConfig?.tutorial_principal_enabled, true);
  return false;
}

function buildStorageKey(user: AuthUser, role: Role | null) {
  return `shine_support_guide:${user.email || user.name || 'user'}:${role || user.role}`;
}

function readProgress(key: string): TutorialProgress {
  try {
    const parsed = JSON.parse(window.localStorage.getItem(key) || '{}') as TutorialProgress;
    return {
      stepIndex: Number.isFinite(Number(parsed.stepIndex)) ? Math.max(0, Number(parsed.stepIndex)) : 0,
      completedAt: parsed.completedAt || undefined,
    };
  } catch {
    return { stepIndex: 0 };
  }
}

function writeProgress(key: string, progress: TutorialProgress) {
  try {
    window.localStorage.setItem(key, JSON.stringify(progress));
  } catch {
    // Local progress is convenience-only.
  }
}

function clearProgress(key: string) {
  try {
    window.localStorage.removeItem(key);
  } catch {
    // Ignore storage failures.
  }
}

function tabAvailable(navTabs: string[], tab?: string) {
  if (!tab) return true;
  return navTabs.includes(tab);
}

function baseOperationalSteps(role: Role, navTabs: string[]): TutorialStep[] {
  const steps: TutorialStep[] = [
    {
      id: 'navigation',
      targetId: 'app-navigation',
      title: 'Your Work Map',
      body: 'The sidebar is your route map. Each tab is a focused work area, and this guide will move through the important ones in order.',
      actionHint: 'Use Next and Previous to move without losing your place.',
    },
  ];

  if (tabAvailable(navTabs, 'dashboard')) {
    steps.push(
      {
      id: 'dashboard-open',
      tab: 'dashboard',
      targetId: 'nav-dashboard',
      title: 'Open Dashboard',
      body: 'Select Dashboard to continue.',
      actionHint: 'Click the highlighted Dashboard button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'dashboard-overview',
        tab: 'dashboard',
        targetId: 'dashboard-overview',
        title: 'Completion Overview',
        body: role === 'hod'
          ? 'Use these cards and tables to monitor your assigned scopes before chasing pending work.'
          : 'Use this overview to read college-wide completion and spot departments that need attention.',
      },
      {
        id: 'dashboard-marks',
        tab: 'dashboard',
        targetId: 'dashboard-marks-completion',
        title: 'Marks Completion',
        body: 'This tells you which counsellors have completed result communication and where follow-up is still needed.',
      },
      {
        id: 'dashboard-notices',
        tab: 'dashboard',
        targetId: 'dashboard-notice-completion',
        title: 'Notice Completion',
        body: 'Use this notice completion block to check pending counsellors before a reminder is sent.',
      },
    );
  }

  if (tabAvailable(navTabs, 'notices')) {
    steps.push(
      {
      id: 'notices-open',
      tab: 'notices',
      targetId: 'nav-notices',
      title: 'Open Notices',
      body: 'Select Notices to continue.',
      actionHint: 'Click the highlighted Notices button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'notice-composer',
        tab: 'notices',
        targetId: 'notice-composer',
        title: 'Create And Allocate',
        body: 'Compose a notice, attach files, and allocate it only to the required department-year scopes.',
      },
      {
        id: 'notice-completion',
        tab: 'notices',
        targetId: 'notice-completion',
        title: 'Completion Tracking',
        body: 'This list shows who has sent the notice and who still needs a reminder.',
      },
      {
        id: 'notice-records',
        tab: 'notices',
        targetId: 'notice-records',
        title: 'Notice Records',
        body: 'Use records to review, edit, or audit notices after allocation.',
      },
    );
  }

  if (tabAvailable(navTabs, 'reports')) {
    steps.push(
      {
      id: 'reports-open',
      tab: 'reports',
      targetId: 'nav-reports',
      title: 'Open Reports',
      body: 'Select Reports to continue.',
      actionHint: 'Click the highlighted Reports button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'reports-workspace',
        tab: 'reports',
        targetId: 'reports-workspace',
        title: 'Reports Workspace',
        body: 'Move from department to year to test details. This is the source of truth before result sending starts.',
      },
    );
  }

  if (tabAvailable(navTabs, 'activity')) {
    steps.push(
      {
      id: 'activity-open',
      tab: 'activity',
      targetId: 'nav-activity',
      title: 'Open Counsellor Activity',
      body: 'Select Counsellor Activity to continue.',
      actionHint: 'Click the highlighted Activity button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'activity-workspace',
        tab: 'activity',
        targetId: 'activity-workspace',
        title: 'Activity Workspace',
        body: 'Choose department, year, semester, and test, then use the completion table to follow up precisely.',
      },
    );
  }

  if (tabAvailable(navTabs, 'users')) {
    steps.push({
      id: 'users-workspace',
      tab: 'users',
      targetId: 'users-workspace',
      title: role === 'principal' ? 'User Directory' : 'Scoped Users',
      body: role === 'principal'
        ? 'Higher officials can inspect the user directory without needing to manage accounts here.'
        : 'HoD-visible user sections help you understand the counsellor accounts connected to your work.',
    });
  }

  if (tabAvailable(navTabs, 'messages')) {
    steps.push(
      {
      id: 'messages-open',
      tab: 'messages',
      targetId: 'nav-messages',
      title: 'Open Message Logs',
      body: 'Select Message Logs to continue.',
      actionHint: 'Click the highlighted Message Logs button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'messages-workspace',
        tab: 'messages',
        targetId: 'messages-workspace',
        title: 'Communication Audit',
        body: 'Filter by date or counsellor and verify sent status without leaving the app.',
      },
    );
  }

  return steps;
}

function counselorSteps(navTabs: string[]): TutorialStep[] {
  const steps: TutorialStep[] = [
    {
      id: 'navigation',
      targetId: 'app-navigation',
      title: 'Your Counsellor Workspace',
      body: 'This sidebar moves you between dashboard, reports, notices, sending, and history.',
      actionHint: 'Nothing is sent during this guide. It only highlights where the controls live.',
    },
  ];

  if (tabAvailable(navTabs, 'recent-tests')) {
    steps.push(
      {
      id: 'recent-tests-open',
      tab: 'recent-tests',
      targetId: 'nav-recent-tests',
      title: 'Open Dashboard',
      body: 'Select Dashboard to continue.',
      actionHint: 'Click the highlighted Dashboard button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'counselor-dashboard',
        tab: 'recent-tests',
        targetId: 'counselor-dashboard',
        title: 'Counsellor Dashboard',
        body: 'The top cards summarize your students, available tests, and communication count.',
      },
      {
        id: 'top-students',
        tab: 'recent-tests',
        targetId: 'counselor-top-students',
        title: 'Top Performing Students',
        body: 'Use this section to quickly recognize the strongest students in your allocation.',
      },
      {
        id: 'improvement-students',
        tab: 'recent-tests',
        targetId: 'counselor-improvement-students',
        title: 'Students Needing Attention',
        body: 'These students should be checked first when you plan support or follow-up.',
      },
      {
        id: 'recent-tests-table',
        tab: 'recent-tests',
        targetId: 'counselor-recent-tests',
        title: 'Recent Tests',
        body: 'Recent tests give you direct access to view marks or begin sending results.',
      },
      {
        id: 'pending-notices',
        tab: 'recent-tests',
        targetId: 'counselor-pending-notices',
        title: 'Pending Notices',
        body: 'Pending notices wait here until they are sent to the students under you.',
      },
    );
  }

  if (tabAvailable(navTabs, 'notices')) {
    steps.push(
      {
      id: 'notices-open',
      tab: 'notices',
      targetId: 'nav-notices',
      title: 'Open Notices',
      body: 'Select Notices to continue.',
      actionHint: 'Click the highlighted Notices button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'counselor-notices',
        tab: 'notices',
        targetId: 'counselor-notices',
        title: 'Notice Records',
        body: 'Use the send action when a notice needs to be delivered through WhatsApp.',
      },
      {
        id: 'notice-send-entry',
        tab: 'notices',
        targetId: 'counselor-notice-send-entry',
        title: 'Send Notice Entry',
        body: 'This starts the notice send workflow for the selected record.',
        actionHint: 'Click Send To WhatsApp. The guide will continue after the notice template page opens.',
        allowClickThrough: true,
        waitForTarget: 2400,
        continueWhenTargetId: 'counselor-notice-send-workspace',
      },
      {
        id: 'notice-send-workspace',
        tab: 'notices',
        targetId: 'counselor-notice-send-workspace',
        title: 'Notice Send Workspace',
        body: 'This workspace shows message text, attachments, students, and WhatsApp controls.',
        actionHint: 'Confirm the caption, attachments, and send mode before starting.',
        waitForTarget: 5000,
      },
      {
        id: 'notice-start-workflow',
        tab: 'notices',
        targetId: 'counselor-notice-start-workflow',
        title: 'Start Notice Workflow',
        body: 'This is the final button before the WhatsApp notice workspace opens.',
        actionHint: 'Press it for the guide only; WhatsApp will not launch during the tutorial.',
        clickToAdvance: true,
        preventTargetAction: true,
        clickHint: 'Press',
        waitForTarget: 5000,
      },
    );
  }

  if (tabAvailable(navTabs, 'test-database')) {
    steps.push(
      {
      id: 'reports-open',
      tab: 'test-database',
      targetId: 'nav-test-database',
      title: 'Open Reports',
      body: 'Select Reports to continue.',
      actionHint: 'Click the highlighted Reports button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'counselor-reports',
        tab: 'test-database',
        targetId: 'counselor-reports',
        title: 'Semester Test Tables',
        body: 'Review tests here before opening a detail view or starting result sending.',
      },
      {
        id: 'result-send-entry',
        tab: 'test-database',
        targetId: 'counselor-send-entry',
        title: 'Send Results Entry',
        body: 'This is the entry point for WhatsApp result sending.',
        actionHint: 'Click Send To WhatsApp. The guide waits until the template page opens.',
        allowClickThrough: true,
        waitForTarget: 2400,
        continueWhenTargetId: 'counselor-send-workspace',
      },
      {
        id: 'send-workspace',
        tab: 'test-database',
        targetId: 'counselor-send-workspace',
        title: 'Send Result Workspace',
        body: 'Verify template variables, the student list, and WhatsApp mode before sending.',
        actionHint: 'This is the inner template page. Start Workflow is the final real-send handoff.',
        waitForTarget: 5000,
      },
      {
        id: 'send-start-workflow',
        tab: 'test-database',
        targetId: 'counselor-send-start-workflow',
        title: 'Start Workflow',
        body: 'This is the final button before the controlled WhatsApp sidebar opens.',
        actionHint: 'Press it for the guide only; WhatsApp will not launch during the tutorial.',
        clickToAdvance: true,
        preventTargetAction: true,
        clickHint: 'Press',
        waitForTarget: 5000,
      },
    );
  }

  if (tabAvailable(navTabs, 'message-history')) {
    steps.push(
      {
      id: 'message-history-open',
      tab: 'message-history',
      targetId: 'nav-message-history',
      title: 'Open Message Logs',
      body: 'Select Message Logs to continue.',
      actionHint: 'Click the highlighted Message Logs button.',
      allowClickThrough: true,
      clickToAdvance: true,
      clickHint: 'Click',
    },
      {
        id: 'message-history',
        tab: 'message-history',
        targetId: 'counselor-message-history',
        title: 'Delivery History',
        body: 'Use this table to confirm delivery status, student names, and send modes.',
      },
    );
  }

  return steps;
}

function buildSteps(user: AuthUser, navTabs: string[]) {
  const role = getTutorialRole(user);
  if (role === 'counselor') return counselorSteps(navTabs);
  if (role === 'hod' || role === 'principal') return baseOperationalSteps(role, navTabs);
  return [] as TutorialStep[];
}

function findTarget(targetId: string) {
  return document.querySelector(`[data-tour-id="${targetId}"]`) as HTMLElement | null;
}

function readRect(target: HTMLElement): TargetRect {
  const rect = target.getBoundingClientRect();
  return {
    top: rect.top,
    left: rect.left,
    width: rect.width,
    height: rect.height,
  };
}

function computeCardPosition(rect: TargetRect | null) {
  if (typeof window === 'undefined') return {};
  if (window.innerWidth <= 768) return {};
  const reservedBottom = 86;
  if (!rect) {
    return {
      left: Math.max(24, (window.innerWidth - 460) / 2),
      top: Math.max(24, (window.innerHeight - reservedBottom - 170) / 2),
    };
  }
  const cardWidth = Math.min(560, window.innerWidth - 48);
  const cardHeight = 170;
  const gap = 14;
  const right = rect.left + rect.width + gap;
  const left = rect.left - cardWidth - gap;
  const bottom = rect.top + rect.height + gap;
  const top = rect.top - cardHeight - gap;
  const clampLeft = (value: number) => Math.max(18, Math.min(window.innerWidth - cardWidth - 18, value));
  const clampTop = (value: number) => Math.max(18, Math.min(window.innerHeight - reservedBottom - cardHeight - 18, value));

  if (right + cardWidth + 18 <= window.innerWidth) return { left: right, top: clampTop(rect.top) };
  if (left >= 18) return { left, top: clampTop(rect.top) };
  if (bottom + cardHeight + reservedBottom + 18 <= window.innerHeight) return { left: clampLeft(rect.left), top: bottom };
  if (top >= 18) return { left: clampLeft(rect.left), top };
  return { left: clampLeft(rect.left), top: clampTop(rect.top + rect.height / 2 - cardHeight / 2) };
}

export function SupportGuideLauncher({
  open,
  user,
  appConfig,
  activeTab,
  navTabs,
  onClose,
  onNavigateTab,
}: SupportGuideLauncherProps) {
  const role = getTutorialRole(user);
  const enabled = isTutorialEnabledForRole(role, appConfig);
  const steps = useMemo(() => buildSteps(user, navTabs), [navTabs, user]);
  const storageKey = useMemo(() => buildStorageKey(user, role), [role, user]);
  const [progress, setProgress] = useState<TutorialProgress>(() => readProgress(storageKey));
  const [running, setRunning] = useState(false);
  const [stepIndex, setStepIndex] = useState(0);
  const [skippedStepIds, setSkippedStepIds] = useState<string[]>([]);
  const [targetRect, setTargetRect] = useState<TargetRect | null>(null);
  const [missingNotice, setMissingNotice] = useState('');
  const [waitingForTarget, setWaitingForTarget] = useState('');
  const [waitingForClick, setWaitingForClick] = useState(false);

  useEffect(() => {
    setProgress(readProgress(storageKey));
  }, [storageKey, open]);

  const step = steps[stepIndex] || null;
  const hasContinue = enabled && !!steps.length && !progress.completedAt && progress.stepIndex > 0 && progress.stepIndex < steps.length;

  const finishGuide = () => {
    const completedAt = new Date().toISOString();
    writeProgress(storageKey, { stepIndex: steps.length, completedAt });
    setProgress({ stepIndex: steps.length, completedAt });
    setRunning(false);
    setStepIndex(0);
    setSkippedStepIds([]);
    setTargetRect(null);
    setWaitingForTarget('');
    setWaitingForClick(false);
    onClose();
  };

  const startGuideAt = (index: number) => {
    if (!enabled || !steps.length) return;
    const safeIndex = Math.max(0, Math.min(steps.length - 1, index));
    setMissingNotice('');
    setWaitingForTarget('');
    setWaitingForClick(false);
    setSkippedStepIds([]);
    setStepIndex(safeIndex);
    setRunning(true);
    writeProgress(storageKey, { stepIndex: safeIndex });
    setProgress({ stepIndex: safeIndex });
  };

  const restartGuide = () => {
    clearProgress(storageKey);
    setProgress({ stepIndex: 0 });
    startGuideAt(0);
  };

  const moveToStep = (nextIndex: number) => {
    if (nextIndex >= steps.length) {
      finishGuide();
      return;
    }
    const safeIndex = Math.max(0, Math.min(steps.length - 1, nextIndex));
    setMissingNotice('');
    setWaitingForTarget('');
    setWaitingForClick(false);
    setStepIndex(safeIndex);
    writeProgress(storageKey, { stepIndex: safeIndex });
    setProgress({ stepIndex: safeIndex });
  };

  useEffect(() => {
    if (!running || !step) return undefined;
    if (step.tab && step.tab !== activeTab && !step.clickToAdvance) {
      onNavigateTab(step.tab);
      setTargetRect(null);
      return undefined;
    }

    let cancelled = false;
    let attempts = 0;
    let cleanupTarget: HTMLElement | null = null;
    let cleanupClick: (() => void) | null = null;
    const maxAttempts = Math.max(6, Math.ceil((step.waitForTarget || 1400) / 100));

    const measure = () => {
      if (cancelled) return;
      const target = findTarget(step.targetId);
      if (!target) {
        attempts += 1;
        if (attempts >= maxAttempts) {
          setSkippedStepIds((prev) => (prev.includes(step.id) ? prev : [...prev, step.id]));
          setMissingNotice(`Skipped "${step.title}" because that section is not visible right now.`);
          window.setTimeout(() => {
            if (!cancelled) moveToStep(stepIndex + 1);
          }, 450);
          return;
        }
        window.setTimeout(measure, 100);
        return;
      }

      cleanupTarget = target;
      target.classList.add('tutorial-spotlight-target');
      if (step.allowClickThrough || step.clickToAdvance || step.continueWhenTargetId) target.classList.add('tutorial-clickable');
      const isNavigationClickStep = Boolean(step.clickToAdvance && step.tab && step.targetId.startsWith('nav-'));
      if (isNavigationClickStep) target.classList.add('tutorial-nav-clickable');
      target.scrollIntoView({ block: 'center', inline: 'nearest', behavior: 'smooth' });
      window.setTimeout(() => {
        if (!cancelled) setTargetRect(readRect(target));
      }, 260);

      if (step.clickToAdvance && !step.continueWhenTargetId) {
        setWaitingForClick(true);
        const handleClick = (event: MouseEvent) => {
          if (cancelled) return;
          if (step.preventTargetAction || isNavigationClickStep) {
            event.preventDefault();
            event.stopPropagation();
            event.stopImmediatePropagation();
          }
          if (step.tab) onNavigateTab(step.tab);
          setWaitingForClick(false);
          window.setTimeout(() => {
            if (!isNavigationClickStep && cancelled) return;
            moveToStep(stepIndex + 1);
          }, isNavigationClickStep ? 160 : step.tab ? 320 : 180);
        };
        const useCapture = Boolean(step.preventTargetAction || isNavigationClickStep);
        target.addEventListener('click', handleClick, { capture: useCapture, once: true });
        cleanupClick = () => target.removeEventListener('click', handleClick, useCapture);
      } else {
        setWaitingForClick(false);
      }

      if (step.continueWhenTargetId) {
        setWaitingForTarget(step.continueWhenTargetId);
        const waitForNextTarget = () => {
          if (cancelled) return;
          const nextTarget = findTarget(step.continueWhenTargetId || '');
          if (nextTarget) {
            moveToStep(stepIndex + 1);
            return;
          }
          window.setTimeout(waitForNextTarget, 250);
        };
        window.setTimeout(waitForNextTarget, 250);
      } else {
        setWaitingForTarget('');
      }
    };

    measure();
    const refresh = () => {
      const target = findTarget(step.targetId);
      if (target) setTargetRect(readRect(target));
    };
    window.addEventListener('resize', refresh);
    window.addEventListener('scroll', refresh, true);

    return () => {
      cancelled = true;
      window.removeEventListener('resize', refresh);
      window.removeEventListener('scroll', refresh, true);
      if (cleanupClick) cleanupClick();
      if (cleanupTarget) {
        cleanupTarget.classList.remove('tutorial-spotlight-target');
        cleanupTarget.classList.remove('tutorial-clickable');
        cleanupTarget.classList.remove('tutorial-nav-clickable');
      }
    };
  }, [activeTab, running, step, stepIndex]);

  if (!open && !running) return null;

  const cardPosition = computeCardPosition(targetRect);
  const progressPct = steps.length ? Math.round(((stepIndex + 1) / steps.length) * 100) : 0;
  const canRunGuide = enabled && steps.length > 0;
  const showClickBeacon = Boolean(targetRect && (step?.clickToAdvance || step?.continueWhenTargetId));

  return (
    <>
      {open && !running ? (
        <div className="modal-overlay open support-guide-launcher-overlay" onClick={onClose}>
          <div className="support-guide-launcher" onClick={(event) => event.stopPropagation()}>
            <div className="support-guide-hero">
              <div>
                <span className="support-guide-eyebrow"><i className="fas fa-compass"></i> Shine Command Guide</span>
                <h3>{getRoleName(role)} Guide</h3>
                <p>
                  A visual walkthrough that highlights the exact controls you need, moves between tabs, and keeps your place.
                </p>
              </div>
              <button type="button" className="modal-close support-guide-close" onClick={onClose} aria-label="Close guide">
                <i className="fas fa-xmark"></i>
              </button>
            </div>

            <div className="support-guide-status-grid">
              <div>
                <span>Role</span>
                <strong>{getRoleName(role)}</strong>
              </div>
              <div>
                <span>Steps</span>
                <strong>{steps.length || '-'}</strong>
              </div>
              <div>
                <span>Status</span>
                <strong>{canRunGuide ? (progress.completedAt ? 'Completed' : hasContinue ? 'In progress' : 'Ready') : 'Unavailable'}</strong>
              </div>
            </div>

            {!role ? (
              <div className="support-guide-note">This guide is currently built for Counsellors, HoDs, and Higher Officials. DEO can be added separately later.</div>
            ) : !enabled ? (
              <div className="support-guide-note">Guided tutorials are turned off for your role by the admin settings.</div>
            ) : null}

            <div className="support-guide-actions">
              <button type="button" className="btn btn-primary" disabled={!canRunGuide} onClick={() => startGuideAt(0)}>
                <i className="fas fa-play"></i> Start Guide
              </button>
              <button type="button" className="btn btn-outline" disabled={!hasContinue} onClick={() => startGuideAt(progress.stepIndex)}>
                <i className="fas fa-forward"></i> Continue
              </button>
              <button type="button" className="btn btn-outline" disabled={!canRunGuide} onClick={restartGuide}>
                <i className="fas fa-rotate-left"></i> Restart
              </button>
              <button type="button" className="btn btn-outline" onClick={onClose}>
                Close
              </button>
            </div>
          </div>
        </div>
      ) : null}

      {running && step ? (
        <div className="tutorial-overlay open spotlight-active" aria-hidden="false">
          {targetRect ? (
            <div
              className="tutorial-highlight support-guide-highlight"
              style={{
                display: 'block',
                top: targetRect.top - 8,
                left: targetRect.left - 8,
                width: targetRect.width + 16,
                height: targetRect.height + 16,
              }}
            />
          ) : null}
          {!showClickBeacon && targetRect ? <div className="support-guide-pointer" style={{
            top: targetRect.top + Math.max(12, targetRect.height / 2 - 12),
            left: Math.min(window.innerWidth - 56, Math.max(12, targetRect.left + targetRect.width + 12)),
          }}>
            <i className="fas fa-arrow-left"></i>
          </div> : null}
          {showClickBeacon && targetRect ? (
            <div
              className="support-guide-click-beacon"
              style={{
                top: Math.max(18, targetRect.top + 8),
                left: Math.max(30, Math.min(window.innerWidth - 70, targetRect.left + Math.min(targetRect.width - 10, Math.max(24, targetRect.width / 2)))),
              }}
            >
              <i className="fas fa-hand-pointer"></i>
              <span>{step.clickHint || 'Click'}</span>
            </div>
          ) : null}
          <div className="tutorial-card support-guide-card" style={cardPosition}>
            <div className="support-guide-card-topline">
              <span>{getRoleName(role)}</span>
              <span>{stepIndex + 1} / {steps.length}</span>
            </div>
            <div className="support-guide-progress">
              <span style={{ width: `${progressPct}%` }}></span>
            </div>
            <h3 className="tutorial-card-title">{step.title}</h3>
            <p className="tutorial-card-text">{step.body}</p>
            {step.actionHint ? <p className="support-guide-action-hint"><i className="fas fa-lightbulb"></i> {step.actionHint}</p> : null}
            {missingNotice || skippedStepIds.length ? (
              <p className="tutorial-card-meta">{missingNotice || `${skippedStepIds.length} unavailable step${skippedStepIds.length === 1 ? '' : 's'} skipped.`}</p>
            ) : waitingForTarget ? (
              <p className="tutorial-card-meta">Waiting for the send workspace to open...</p>
            ) : waitingForClick ? (
              <p className="tutorial-card-meta">Waiting for your click...</p>
            ) : (
              <p className="tutorial-card-meta">Step {stepIndex + 1} of {steps.length}</p>
            )}
            <div className="tutorial-actions">
              <button type="button" className="btn btn-outline btn-sm" disabled={stepIndex <= 0} onClick={() => moveToStep(stepIndex - 1)}>
                Previous
              </button>
              <button type="button" className="btn btn-outline btn-sm" onClick={() => {
                setRunning(false);
                setTargetRect(null);
                onClose();
              }}>
                Skip
              </button>
              <button type="button" className="btn btn-primary btn-sm" disabled={Boolean(waitingForTarget || waitingForClick)} onClick={() => moveToStep(stepIndex + 1)}>
                {waitingForTarget || waitingForClick ? 'Waiting...' : stepIndex >= steps.length - 1 ? 'Finish' : 'Next'}
              </button>
            </div>
          </div>
        </div>
      ) : null}
    </>
  );
}

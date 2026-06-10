import { COUNTRY_CODE } from './config.js';

const NOT_ATTENDED_KEYS = new Set(['examnotattended', 'notattended', 'absentcount', 'noofsubjectsabsent']);
const GPA_KEYS = new Set(['gpa', 'cgpa']);
const FAILED_KEYS = new Set(['noofsubjectsfailed', 'failedsubjects', 'failedcount', 'nooffailedsubjects']);

function normalizeMetricKey(key: string) {
  return String(key || '').toLowerCase().replace(/[^a-z0-9]/g, '');
}

function getMetricValue(metricKey: string, marks: Record<string, string>) {
  const normalizedToValue: Record<string, string> = {};
  for (const [rawKey, rawValue] of Object.entries(marks || {})) {
    normalizedToValue[normalizeMetricKey(rawKey)] = String(rawValue ?? '').trim();
  }

  if (metricKey === 'failed_subjects') {
    const found = Array.from(FAILED_KEYS).find((key) => normalizedToValue[key] !== undefined);
    return found ? normalizedToValue[found] : '';
  }
  if (metricKey === 'not_attended') {
    const found = Array.from(NOT_ATTENDED_KEYS).find((key) => normalizedToValue[key] !== undefined);
    return found ? normalizedToValue[found] : '';
  }
  if (metricKey === 'gpa') {
    const found = Array.from(GPA_KEYS).find((key) => normalizedToValue[key] !== undefined);
    return found ? normalizedToValue[found] : '';
  }
  return '';
}

function getSubjectValue(orderItem: { raw_key?: string; normalized_key?: string }, marks: Record<string, string>) {
  if (orderItem.raw_key && Object.prototype.hasOwnProperty.call(marks, orderItem.raw_key)) {
    return String(marks[orderItem.raw_key] ?? '').trim();
  }
  const entry = Object.entries(marks || {}).find(([key]) => normalizeMetricKey(key) === String(orderItem.normalized_key || ''));
  return entry ? String(entry[1] ?? '').trim() : '';
}

export function buildParentSubjectsTable(
  marks: Record<string, string>,
  orderedFields?: Array<{ type?: string; raw_key?: string; normalized_key?: string; key?: string }>,
) {
  const lines: string[] = [];

  if (Array.isArray(orderedFields)) {
    for (const item of orderedFields) {
      if (!item) continue;
      if (String(item.type || '').trim().toLowerCase() === 'metric') {
        const metricKey = String(item.key || item.normalized_key || '').trim();
        const label =
          metricKey === 'failed_subjects' ? 'Failed Subjects' : metricKey === 'not_attended' ? 'No of Subjects Absent' : metricKey === 'gpa' ? 'GPA' : metricKey;
        const value = getMetricValue(metricKey, marks);
        if (String(value || '').trim()) {
          lines.push(`${label} : ${value}`.trim());
        }
        continue;
      }

      const label = String(item.raw_key || item.normalized_key || 'Subject').trim();
      const value = getSubjectValue(item, marks);
      if (String(value || '').trim()) {
        lines.push(`${label} : ${value}`.trim());
      }
    }
  }

  if (lines.length) return lines.join('\n').trim();

  for (const [subject, value] of Object.entries(marks || {})) {
    if (!String(value ?? '').trim()) continue;
    lines.push(`${subject} : ${value}`.trim());
  }
  return lines.join('\n').trim();
}

export function buildParentMessage(testName: string, regNo: string, studentName: string, marks: Record<string, string>) {
  const marksTable = buildParentSubjectsTable(marks);
  return (
    `Dear Parent , The Following is the ${testName} Marks Secured in each Course by your son/daughter\n\n` +
    `REGISTER NUMBER :  ${regNo}\n` +
    `NAME : ${studentName}\n\n` +
    `${marksTable}\n\n` +
    `Regards\n` +
    `PRINCIPAL\n` +
    `RMKCET`
  );
}

export function fillTemplate(template: string, variables: Record<string, string>) {
  let output = String(template || '');
  for (const [key, value] of Object.entries(variables || {})) {
    output = output.replaceAll(`{${key}}`, String(value ?? ''));
  }
  return output;
}

export function getWhatsappLink(phoneNumber: string, message: string) {
  const phone = String(phoneNumber || '').replace(/\D/g, '').slice(-10);
  const cc = String(COUNTRY_CODE || '91').replace(/\D/g, '') || '91';
  const fullPhone = `${cc}${phone}`;
  return `whatsapp://send?phone=${fullPhone}&text=${encodeURIComponent(message)}`;
}

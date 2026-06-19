import { spawn } from 'node:child_process';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { resolve } from 'node:path';
import { SERVER_ROOT } from './config.js';

export type CellObject = {
  v?: unknown;
  w?: string;
  s?: {
    fgColor?: {
      rgb?: string;
      indexed?: string | number;
    };
  };
};

export type WorkSheet = {
  [cellAddress: string]: CellObject | unknown[][] | number | undefined;
  __rows?: unknown[][];
  __maxRow?: number;
  __maxColumn?: number;
};

export type WorkBook = {
  SheetNames: string[];
  Sheets: Record<string, WorkSheet>;
};

const WORKBOOK_SCRIPT = resolve(SERVER_ROOT, 'scripts', 'read_workbook.py');

function runPythonWorkbookReader(filePath: string) {
  const commands =
    process.platform === 'win32'
      ? [
          { command: 'python', args: [WORKBOOK_SCRIPT, filePath] },
          { command: 'py', args: ['-3', WORKBOOK_SCRIPT, filePath] },
        ]
      : [
          { command: 'python3', args: [WORKBOOK_SCRIPT, filePath] },
          { command: 'python', args: [WORKBOOK_SCRIPT, filePath] },
        ];

  const run = (command: string, args: string[]) => new Promise<string>((resolvePromise, rejectPromise) => {
    const child = spawn(command, args, {
      cwd: SERVER_ROOT,
      stdio: ['ignore', 'pipe', 'pipe'],
      windowsHide: true,
    });
    let stdout = '';
    let stderr = '';
    child.stdout.on('data', (chunk) => { stdout += chunk.toString(); });
    child.stderr.on('data', (chunk) => { stderr += chunk.toString(); });
    child.on('error', rejectPromise);
    child.on('close', (code) => {
      if (code === 0) {
        resolvePromise(stdout);
        return;
      }
      rejectPromise(new Error(stderr.trim() || stdout.trim() || `Workbook reader exited with code ${code}.`));
    });
  });

  return (async () => {
    let lastError: Error | null = null;
    for (const attempt of commands) {
      try {
        return await run(attempt.command, attempt.args);
      } catch (error) {
        lastError = error instanceof Error ? error : new Error('Workbook reader failed.');
      }
    }
    throw lastError || new Error('Python runtime not available for workbook parsing.');
  })();
}

export async function readWorkbook(buffer: Buffer | ArrayBuffer, originalFilename = 'workbook.xlsx'): Promise<WorkBook> {
  const bytes = Buffer.isBuffer(buffer) ? buffer : Buffer.from(buffer);
  const tempDir = await mkdtemp(resolve(tmpdir(), 'shine-workbook-'));
  const safeName = String(originalFilename || 'workbook.xlsx').replace(/[^\w.\-]+/g, '_') || 'workbook.xlsx';
  const tempFilePath = resolve(tempDir, safeName);
  try {
    await writeFile(tempFilePath, bytes);
    const raw = await runPythonWorkbookReader(tempFilePath);
    const parsed = JSON.parse(raw) as {
      sheetNames?: string[];
      sheets?: Record<string, { rows?: unknown[][]; cells?: Record<string, CellObject>; maxRow?: number; maxColumn?: number }>;
    };
    const sheetNames = Array.isArray(parsed.sheetNames) ? parsed.sheetNames : [];
    const sheets: Record<string, WorkSheet> = {};
    for (const sheetName of sheetNames) {
      const source = parsed.sheets?.[sheetName] || {};
      sheets[sheetName] = {
        ...(source.cells || {}),
        __rows: Array.isArray(source.rows) ? source.rows : [],
        __maxRow: Number(source.maxRow || 0) || 0,
        __maxColumn: Number(source.maxColumn || 0) || 0,
      };
    }
    return { SheetNames: sheetNames, Sheets: sheets };
  } finally {
    await rm(tempDir, { recursive: true, force: true }).catch(() => undefined);
  }
}

export function encodeCell(address: { r: number; c: number }) {
  let column = Number(address.c || 0);
  let label = '';
  do {
    label = String.fromCharCode(65 + (column % 26)) + label;
    column = Math.floor(column / 26) - 1;
  } while (column >= 0);
  return `${label}${Number(address.r || 0) + 1}`;
}

export function readSheetCell(sheet: WorkSheet, address: string): CellObject | undefined {
  const value = sheet[address];
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  return value as CellObject;
}

export function sheetToJson<T = unknown>(sheet: WorkSheet, options: { header?: 1; defval?: unknown; raw?: boolean } = {}) {
  const rows = Array.isArray(sheet.__rows) ? sheet.__rows : [];
  const defval = Object.prototype.hasOwnProperty.call(options, 'defval') ? options.defval : undefined;
  if (options.header === 1) {
    return rows.map((row) => {
      const source = Array.isArray(row) ? row : [];
      const next = source.map((value) => value ?? defval);
      if (defval === undefined) {
        while (next.length && (next[next.length - 1] === undefined || next[next.length - 1] === null || next[next.length - 1] === '')) {
          next.pop();
        }
      }
      if (options.raw === false) {
        return next.map((value) => value == null ? '' : String(value)) as T;
      }
      return next as T;
    });
  }

  const headerRow = Array.isArray(rows[0]) ? rows[0] : [];
  const headers = headerRow.map((value, index) => String(value ?? `Column ${index + 1}`).trim() || `Column ${index + 1}`);
  return rows.slice(1).map((row) => {
    const source = Array.isArray(row) ? row : [];
    const item: Record<string, unknown> = {};
    headers.forEach((header, index) => {
      item[header] = source[index] ?? defval ?? '';
    });
    return item as T;
  });
}

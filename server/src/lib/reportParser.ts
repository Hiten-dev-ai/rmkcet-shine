import { spawn } from 'node:child_process';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { resolve } from 'node:path';
import { SERVER_ROOT } from './config.js';

export interface ParsedMarksheetStudent {
  reg_no: string;
  name: string;
  department?: string;
  phone?: string;
  email?: string;
  marks: Record<string, string>;
  section?: string;
}

export interface ParsedMarksheetPayload {
  testInfo: {
    test_name: string;
    semester: number;
    academic_year: string;
    batch_name: string;
    department: string;
    section: string;
    subjects: Array<{ name: string; code: string }>;
    subject_columns: Record<string, string>;
    header_row: number;
    data_start_row: number;
    max_marks: number;
  };
  students: ParsedMarksheetStudent[];
  errors: string[];
}

const PARSER_SCRIPT = resolve(SERVER_ROOT, 'scripts', 'parse_marksheet.py');

function runProcess(command: string, args: string[]) {
  return new Promise<{ stdout: string; stderr: string }>((resolvePromise, rejectPromise) => {
    const child = spawn(command, args, {
      cwd: SERVER_ROOT,
      stdio: ['ignore', 'pipe', 'pipe'],
      windowsHide: true,
    });

    let stdout = '';
    let stderr = '';

    child.stdout.on('data', (chunk) => {
      stdout += chunk.toString();
    });
    child.stderr.on('data', (chunk) => {
      stderr += chunk.toString();
    });
    child.on('error', rejectPromise);
    child.on('close', (code) => {
      if (code === 0) {
        resolvePromise({ stdout, stderr });
        return;
      }
      rejectPromise(new Error(stderr.trim() || stdout.trim() || `Parser exited with code ${code}.`));
    });
  });
}

async function runParserWithFallback(tempFilePath: string, originalFilename: string) {
  const commands =
    process.platform === 'win32'
      ? [
          { command: 'python', args: [PARSER_SCRIPT, tempFilePath, originalFilename] },
          { command: 'py', args: ['-3', PARSER_SCRIPT, tempFilePath, originalFilename] },
        ]
      : [
          { command: 'python3', args: [PARSER_SCRIPT, tempFilePath, originalFilename] },
          { command: 'python', args: [PARSER_SCRIPT, tempFilePath, originalFilename] },
        ];

  let lastError: Error | null = null;
  for (const attempt of commands) {
    try {
      return await runProcess(attempt.command, attempt.args);
    } catch (error) {
      lastError = error instanceof Error ? error : new Error('Unknown parser error.');
    }
  }

  throw lastError || new Error('Python runtime not available for marksheet parsing.');
}

export async function parseUploadedMarksheet(originalFilename: string, bytes: Buffer) {
  const tempDir = await mkdtemp(resolve(tmpdir(), 'shine-rebuild-'));
  const tempFilePath = resolve(tempDir, originalFilename || 'upload.xlsx');

  try {
    await writeFile(tempFilePath, bytes);
    const result = await runParserWithFallback(tempFilePath, originalFilename || 'upload.xlsx');
    const parsed = JSON.parse(result.stdout) as ParsedMarksheetPayload;
    parsed.errors = Array.isArray(parsed.errors) ? parsed.errors : [];
    parsed.students = Array.isArray(parsed.students) ? parsed.students : [];
    return parsed;
  } catch (error) {
    throw error instanceof Error ? error : new Error('Failed to parse marksheet.');
  } finally {
    await rm(tempDir, { recursive: true, force: true }).catch(() => undefined);
  }
}

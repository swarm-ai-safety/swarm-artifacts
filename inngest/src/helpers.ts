/**
 * SWARM Research OS — Shared helpers for Inngest functions.
 *
 * Shell-out utilities, path constants, and common operations.
 */

import { execFile } from "node:child_process";
import { readFile, access } from "node:fs/promises";
import { resolve } from "node:path";
import { promisify } from "node:util";
import YAML from "yaml";

const execFileAsync = promisify(execFile);

// ── Paths ─────────────────────────────────────────────────────────────

/** Root of the swarm-artifacts repo. Override with SWARM_ARTIFACTS_ROOT. */
export const REPO_ROOT = process.env.SWARM_ARTIFACTS_ROOT
  ?? resolve(import.meta.dirname ?? ".", "..");

export const RUNS_DIR = resolve(REPO_ROOT, "runs");
export const VAULT_DIR = resolve(REPO_ROOT, "vault");
export const SCRIPTS_DIR = resolve(REPO_ROOT, "scripts");
export const SCENARIOS_DIR = resolve(REPO_ROOT, "scenarios");

// ── Shell helpers ─────────────────────────────────────────────────────

export interface ExecResult {
  stdout: string;
  stderr: string;
  exitCode: number;
}

/** Run a command, returning stdout/stderr/exit. Never throws. */
export async function exec(
  cmd: string,
  args: string[],
  opts?: { cwd?: string; timeout?: number },
): Promise<ExecResult> {
  try {
    const { stdout, stderr } = await execFileAsync(cmd, args, {
      cwd: opts?.cwd ?? REPO_ROOT,
      timeout: opts?.timeout ?? 600_000, // 10 min default
      maxBuffer: 50 * 1024 * 1024,      // 50 MB
    });
    return { stdout, stderr, exitCode: 0 };
  } catch (err: unknown) {
    const e = err as { stdout?: string; stderr?: string; code?: number };
    return {
      stdout: e.stdout ?? "",
      stderr: e.stderr ?? String(err),
      exitCode: e.code ?? 1,
    };
  }
}

/** Run a Python script from scripts/. */
export async function runScript(name: string, args: string[] = []): Promise<ExecResult> {
  return exec("python", [resolve(SCRIPTS_DIR, name), ...args]);
}

/** Run a SWARM command. */
export async function runSwarm(args: string[], opts?: { timeout?: number }): Promise<ExecResult> {
  return exec("python", ["-m", "swarm", ...args], opts);
}

// ── File helpers ──────────────────────────────────────────────────────

export async function fileExists(path: string): Promise<boolean> {
  try {
    await access(path);
    return true;
  } catch {
    return false;
  }
}

export async function readJson<T = unknown>(path: string): Promise<T> {
  const raw = await readFile(path, "utf-8");
  return JSON.parse(raw) as T;
}

export async function readYaml<T = unknown>(path: string): Promise<T> {
  const raw = await readFile(path, "utf-8");
  return YAML.parse(raw) as T;
}

// ── Git helpers ───────────────────────────────────────────────────────

export async function gitAdd(files: string[]): Promise<ExecResult> {
  return exec("git", ["add", ...files]);
}

export async function gitCommit(message: string): Promise<ExecResult> {
  return exec("git", ["commit", "-m", message]);
}

export async function gitPush(): Promise<ExecResult> {
  return exec("git", ["push"]);
}

export async function gitCurrentSha(): Promise<string> {
  const { stdout } = await exec("git", ["rev-parse", "--short", "HEAD"]);
  return stdout.trim();
}

/** Create a branch, stage files, commit, push, and open a PR via gh. */
export async function createPR(opts: {
  branch: string;
  title: string;
  body: string;
  files: string[];
}): Promise<{ pr_number: number; pr_url: string }> {
  // Create and checkout branch
  await exec("git", ["checkout", "-b", opts.branch]);

  // Stage and commit
  await gitAdd(opts.files);
  await gitCommit(opts.title);
  await gitPush();

  // Open PR
  const { stdout } = await exec("gh", [
    "pr", "create",
    "--title", opts.title,
    "--body", opts.body,
    "--head", opts.branch,
  ]);

  // Parse PR URL from gh output
  const url = stdout.trim();
  const prMatch = url.match(/\/pull\/(\d+)/);
  const pr_number = prMatch ? parseInt(prMatch[1], 10) : 0;

  // Return to main
  await exec("git", ["checkout", "main"]);

  return { pr_number, pr_url: url };
}

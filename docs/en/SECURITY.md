# Security policy

[English](SECURITY.md) · [简体中文](../zh-CN/SECURITY.md) ·
[日本語](../ja/SECURITY.md) · [Esperanto](../eo/SECURITY.md)

Ript is a formal research library, not a hosted service. Security covers proof
trust, executable examples, dependency and CI integrity, and unsafe behavior
that could affect consumers.

## Supported versions

Only current `main` is supported. Include the exact commit SHA and pinned Lean
toolchain in every report; there is no release backport policy.

## Private reporting

Use GitHub's **Security** tab and private vulnerability reporting when
available. Otherwise open a public issue containing only a request for a
private channel. Never publish exploit details, credentials, or private data.

Include the affected module and commit, impact, realistic threat scenario,
minimal reproduction, affected trust boundary, and known mitigation.

## Security scope

Security issues include trust escapes, hidden axioms, unsafe declarations,
quality-gate bypasses, reachable dependency/CI compromise, executable boundary
violations, secret exposure, and private-data leaks. A documented conjecture,
modeling disagreement, or unstable API is normally a research or bug report.

## Response and disclosure

Reports are handled on a best-effort basis without a guaranteed SLA. Fixes
must pass the normal kernel, audit, and CI requirements. Coordinate disclosure
until a fix or mitigation is available.

See the canonical root [security policy](../../SECURITY.md).

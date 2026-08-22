# Security policy

[English](docs/en/SECURITY.md) · [简体中文](docs/zh-CN/SECURITY.md) ·
[日本語](docs/ja/SECURITY.md) · [Esperanto](docs/eo/SECURITY.md)

Ript is a formal research library, not a hosted service. Security work focuses
on the integrity of the proof boundary, executable examples, dependency and CI
supply chain, and unsafe behavior in code that consumers may execute.

## Supported versions

Only the current `main` branch is supported. Ript has no stable releases or
backport policy. Reports should name the exact commit SHA and pinned toolchain.

## Report privately

Use GitHub's **Security** tab and private vulnerability reporting when it is
available. If GitHub does not offer a private form, open a public issue that
contains only a request for a private contact channel—do not include exploit
details, credentials, or unpublished vulnerability information.

Include:

- affected commit and module;
- impact and realistic threat scenario;
- minimal reproduction or proof of concept;
- whether the issue affects kernel trust, generated executable code, CI,
  dependencies, or documentation only;
- any known mitigation.

## What counts as a security issue

- a proof-trust escape, hidden project axiom, unsafe declaration, or way to
  bypass the documented quality gate;
- executable code that violates its stated input or resource boundary;
- compromised or unpinned CI/dependency behavior;
- accidental secret or private-data exposure;
- a dependency vulnerability that is reachable from Ript's supported use.

A disagreement about a mathematical model, an unproved conjecture already
listed as open, or an API instability is normally a research or bug report,
not a security vulnerability.

## Response and disclosure

The maintainer will acknowledge and triage reports on a best-effort basis;
early-stage research software has no guaranteed service-level agreement. Fixes
must preserve the same kernel, axiom-audit, and CI requirements as other
changes. Coordinate public disclosure until a fix or documented mitigation is
available.

Never include secrets in an issue, pull request, test fixture, or Lean trace.

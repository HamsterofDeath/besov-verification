# Repository instructions

## Agent roles

The organizer (also called coordinator, orchestrator, or managing supervisor) is dispatch-only: route assignments, immediately refill eligible capacity, read brief bounded ownership/allocation/status results, and report. Dispatch every discovered task or blocker to a bounded owner; never take it over while waiting. Provisioning and recovery owners prepare or recycle exclusive worktrees and resources. Implementers perform feature work and implementation validation. Independent reviewers use a different checked identity to review the exact commit and record authenticated verdicts. A dedicated integrator performs integrated checks, captures and packages integration evidence, uploads it, lands through the guarded serialized repository path, and reads back Done with no remaining claim where a taskboard is used.

The organizer never implements, tests, audits, captures, packages or uploads evidence, prepares or recycles worktrees, repairs environments, acquires implementation/review/integration claims, or lands changes. Instructions below that call for those operations apply to the assigned execution owner. Every owner keeps its own checked identity and required claim, with an exclusive worktree and one feature branch. Preserve independent exact-commit review, all quality and security gates, guarded pushes, and serialized landing; never use pull requests, force pushes, shared credentials, or an unreviewed direct push to main/master.

## Local-only validation

- Never run CI in GitHub Actions or any other GitHub-hosted workflow for this project.
- Run all builds, tests, lint, coverage, release checks, and other validation locally.
- Do not add, enable, trigger, or rely on GitHub CI workflows or required GitHub status checks.
- When legacy push-triggered workflows still exist, include [skip ci] in every pushed commit message.
- Record the local validation commands and results in the relevant ticket or handoff.

# Repository instructions

## Local-only validation

- Never run CI in GitHub Actions or any other GitHub-hosted workflow for this project.
- Run all builds, tests, lint, coverage, release checks, and other validation locally.
- Do not add, enable, trigger, or rely on GitHub CI workflows or required GitHub status checks.
- When legacy push-triggered workflows still exist, include [skip ci] in every pushed commit message.
- Record the local validation commands and results in the relevant ticket or handoff.

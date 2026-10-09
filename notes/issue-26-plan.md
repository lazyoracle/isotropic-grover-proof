# Issue #26 Plan: Prevent docgen-action from falsely triggering Jekyll build

## Tasks
1. [x] Inspect issue #26, workflow `.github/workflows/lean_action_ci.yml`, and `docs/`.
2. [x] Create design doc `notes/issue-26-design.md` and plan doc `notes/issue-26-plan.md`.
3. [x] Rename `docs/` to `notes/` via `git mv docs notes`.
4. [x] Update `.github/workflows/lean_action_ci.yml` with `with: homepage: '.pages'`.
5. [x] Run `lake build` to confirm project build integrity.
6. [x] Review git diff.
7. [ ] Commit with message `fix(ci): prevent docgen-action from falsely triggering Jekyll build (closes #26)`.
8. [ ] Push branch `issue-26` to `origin`.
9. [ ] Create PR using `gh pr create`.
10. [ ] Add review comment using `gh pr review --comment`.
11. [ ] Wait for CI check to pass on the PR.
12. [ ] Rebase onto `origin/main` if needed.
13. [ ] Squash and merge PR (`gh pr merge --squash --delete-branch`).
14. [ ] Verify issue #26 is closed.

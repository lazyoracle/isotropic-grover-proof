# Issue #26 Design Document: Prevent docgen-action from falsely triggering Jekyll build

## Problem Context
In GitHub Actions workflow `.github/workflows/lean_action_ci.yml`, the workflow uses `leanprover-community/docgen-action@v1`.
By default, `docgen-action@v1` sets the input `homepage` to `"docs"`.
During execution, `docgen-action` executes:
```bash
if [ -d ${{ inputs.homepage }} ]; then
  echo "DOCS_EXISTS=true" >> $GITHUB_ENV
fi
```
When `DOCS_EXISTS=true`, `docgen-action` assumes the directory is a Jekyll site and runs:
```bash
JEKYLL_ENV=production bundle exec jekyll build
```
Commit `da43113` introduced the `docs/` directory to store internal markdown design and planning notes.
Because `docs/` existed, `docgen-action` assumed it was a Jekyll documentation source and attempted to run `bundle exec jekyll build`, failing with:
```
Could not locate Gemfile or .bundle/ directory
Error: Process completed with exit code 10.
```

## Solution Design
1. **Relocate Internal Design Docs**:
   Rename the repository's `docs/` directory to `notes/`.
   This keeps all design documents and implementation plans organized without colliding with standard documentation conventions or tool defaults like `docgen-action`'s default `docs`.

2. **Explicitly Configure `homepage` in `lean_action_ci.yml`**:
   In `.github/workflows/lean_action_ci.yml`, explicitly set `with: homepage: '.pages'` for `leanprover-community/docgen-action@v1`.
   Because `.pages` does not exist in the repository root, `[ -d .pages ]` evaluates to false, setting `DOCS_EXISTS=false`.
   `docgen-action` will then generate Lean API documentation into `.pages/docs` and deploy to GitHub Pages without attempting to run Jekyll.

## Verification
- Verify `docs/` is moved to `notes/` cleanly in git.
- Verify `.github/workflows/lean_action_ci.yml` contains `with: homepage: '.pages'`.
- Run `lake build` to confirm Lean code compiles cleanly.
- Push and open PR; verify CI check runs successfully without Jekyll error.

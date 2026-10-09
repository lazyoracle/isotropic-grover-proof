## Scientific goals

The scientific goals and the repository structure of the project are outlined in README.md, pending work is tracked in Github issues.

## Development process

Every new feature or bug fix must adhere to the following general outline:
1. A github issue describes the request and defines the scope and/or definition of success.
2. All issue related work including brainstorming, spec definition and plan writing happens in isolated worktrees that live inside `.claude/worktrees/` subdirectory from the root of the repo. This allows simultaneous working on many different issues by different parallel agents in different worktrees.
3. Absolutely no changes should be made in the main checkout of the repository, make sure all sub-agents strictly follow this instruction and always work only in the isolated worktree for the session.
4. `superpowers:brainstorming` to better understand the request and clarify any open questions and get all assumptions and design choices codified into a design document.
5. `superpowers:writing-plans` to come up with a detailed step by step plan that breaks down the issue into manageable individual tasks.
6. Each task is developed in a `subagent-driven development` and `test-driven development` process using the appropriate skills.
7. When development is finished, the `finishing-a-development-branch` skill verifies tests and then runs a final review.
8. `code-simplifier:code-simplifier` agent is triggered at this point to identify and implement any simplifications possible for the changes made in this worktree
9. At this point, a github pull request is opened for the worktree.
10. If a PR falls behind main and gets a merge conflict, resolve by rebasing the branch onto main while resolving any merge conflicts and force-pushing — do not resolve merge conflicts with a merge commit.
11. `/code-review --comment` skill is triggered to review all the work done in the PR and post the review as inline comments on the github pull request.
12. A sub-agent is dispatched to address all the inline review comments on the PR, including fixes and replying to the individual inline comments, then mark them as resolved.
13. After all comments have been addressed and the CI is green for all checks, every pull request is merged using squash-and-merge only. No merge commits.
14. Make sure the corresponding issue is closed.
15. Make sure the worktree is cleaned up and your local main is synced with remote.

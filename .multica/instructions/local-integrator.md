Integrate reviewed work locally. You never push, open pull requests, or use GitHub. Follow the epic-process skill.

## Epic lines
An epic description can contain these lines. Read them from the epic: the parent issue for a task, or the issue itself when it is an epic.
- "Base branch: <branch>": the branch the epic starts from and finally merges into. Default: main.
- "Final integration: local": merge the finished epic into the base branch locally, also in a PR workflow.
- "Plan file: <path>": a plan document to keep up to date.

## Source and target
- Task with a parent epic: source = the reviewed SHA in the latest Agent Review comment. Target = epic/<PARENT-ID>. If the target does not exist, create it from the epic's base branch without checking it out: git branch epic/<PARENT-ID> <base branch>.
- Epic (an issue with sub-issues): source = epic/<ISSUE-ID>. Target = its base branch. An epic reaches Integrate only after a human review. If its latest comments show no human approval, do not merge; comment and stop. In a PR workflow, merge an epic only if it has "Final integration: local"; otherwise comment and move it to In Review.
- Task without an epic: target = main (local workflow only). In a PR workflow, do not merge it; comment and move it to In Review.

## Merge in your own worktree
Never check out the target branch, and never change any other agent's branch.
1. OLD=$(git rev-parse <target>); git switch --detach $OLD.
2. git merge --no-ff <source> with a message that names the issue. For an epic into its base branch, if the base moved since the epic started, this also brings the new base commits in.
3. Plan file (only for a task in an epic that has "Plan file:"): mark the items this task completed as done in the plan file, add the issue identifier and the merged source SHA next to them, and commit only that file ("docs(plan): <issue> done"). Do not change anything else in the plan.
4. Do not repeat the review. The coder ran the checks and the Reviewer approved them. Compare the merged tree with the reviewed tree: git diff --quiet <reviewed SHA> HEAD -- . ':(exclude)<plan file>' (for an epic, compare with the epic head).
   - No difference (the target did not move after the coder's base): do not build or test. Continue.
   - Difference (other work was merged in the meantime, or the base moved): run only the quickest build command the project defines, once. No test suites, sweeps or coverage. If it fails, treat it like a merge conflict.
5. Move the target forward from OLD only:
   - Find where the target is checked out: git worktree list --porcelain.
   - If it is checked out in a worktree (for example the project directory or a human's worktree), run git -C <that worktree> merge --ff-only <new-SHA> there. This moves the branch and its files together.
   - If it is not checked out anywhere, run git update-ref refs/heads/<target> <new-SHA> $OLD. This fails if another merge moved the branch; then start again from step 1.
   - If git refuses (not a fast-forward, or local changes in that worktree would be overwritten), do not force it. Comment with the exact error and move the issue to needs_help.
6. Switch back to your own branch (git switch -).

## Result
On success, post a comment with the source, the target branch, the new target SHA, and the plan file change if any. Then move the issue to the next status your workflow step names (Done).
On a merge conflict or a test failure, do not resolve it in a way that changes the coder's intent. Run git merge --abort if needed, post the conflicting files or failing output, and send the issue back to Todo.

Never force anything: no force push, no git reset of shared branches, no git branch -f, no deleting branches. Do not edit code except to resolve trivial merge conflicts; the plan file update above is the only other edit you make. Do not read, expose, or persist credentials. Report blockers instead of working around access limits.
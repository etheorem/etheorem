#!/usr/bin/env python3
"""Bump the patch (Z) component of LeanSha256's version, commit, and tag.

Reads `packages/LeanSha256/lakefile.toml`, increments the third
component of its `version = "X.Y.Z"` field, commits the change on
the current branch, and creates a `leansha256-vX.Y.Z` annotated tag
pointing at that commit.

Does *not* push — prints the exact `git push` commands for `main`
and the tag at the end so the maintainer pushes manually after a
visual review. The mirror workflow on the umbrella picks the tag up
and translates it to `vX.Y.Z` on `github.com/etheorem/LeanSha256`.

Refuses to run if:
  - The working tree has any uncommitted changes (staged or not)
  - The current branch is not `main` (override with `--allow-branch`)
  - The would-be tag already exists locally or on the origin remote

Stdlib-only; no external Python dependencies. Run from any CWD:

    python3 packages/LeanSha256/scripts/bump_patch.py

or via the umbrella Justfile shortcut:

    just leansha256-bump-patch

Minor (Y) and major (X) bumps are deliberately not supported — they
represent decisions the maintainer should make by editing
`lakefile.toml` directly. Patch bumps are the high-frequency case
worth scripting.
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path
from typing import NoReturn


PKG_ROOT = Path(__file__).resolve().parent.parent
LAKEFILE = PKG_ROOT / "lakefile.toml"
REPO_ROOT = PKG_ROOT.parent.parent

# Matches the single `version = "X.Y.Z"` line at top-level of the
# lakefile. Anchored with `^…$` + MULTILINE so we don't accidentally
# rewrite a version string that appears inside a comment or another
# field. Tolerates extra spacing around the `=` for robustness.
VERSION_RE = re.compile(r'^(version\s*=\s*")(\d+)\.(\d+)\.(\d+)(")$', re.M)


def git(*args: str, capture: bool = True) -> str:
    """Run `git <args>` from the repo root.

    Read-only queries default to capturing stdout (returned trimmed).
    For mutating commands (add, commit, tag) pass `capture=False` so
    git's own output streams through to the terminal.
    """
    result = subprocess.run(
        ["git", *args],
        check=True,
        cwd=REPO_ROOT,
        capture_output=capture,
        text=True,
    )
    return result.stdout.strip() if capture else ""


def die(msg: str) -> NoReturn:
    print(f"bump_patch: {msg}", file=sys.stderr)
    sys.exit(1)


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Bump LeanSha256 patch version, commit, and tag.",
    )
    parser.add_argument(
        "--allow-branch",
        action="store_true",
        help="Allow bumping from a branch other than `main`.",
    )
    args = parser.parse_args()

    # Guard 1: clean working tree. The version bump is itself a
    # commit; running it on top of unrelated unstaged work would
    # silently bundle that work into the release commit.
    status = git("status", "--porcelain")
    if status:
        die(
            "working tree has uncommitted changes — commit or stash before "
            "bumping. `git status` output:\n" + status
        )

    # Guard 2: branch is main (releases come off main). The escape
    # hatch is intended for testing the script itself, not for
    # routine use.
    branch = git("rev-parse", "--abbrev-ref", "HEAD")
    if branch != "main" and not args.allow_branch:
        die(
            f"current branch is `{branch}`, not `main`. "
            "Use --allow-branch to override (e.g. for testing)."
        )

    # Parse + bump the version.
    text = LAKEFILE.read_text()
    match = VERSION_RE.search(text)
    if not match:
        die(f'could not find `version = "X.Y.Z"` in {LAKEFILE}')
    major, minor, patch = int(match[2]), int(match[3]), int(match[4])
    new_version = f"{major}.{minor}.{patch + 1}"
    tag = f"leansha256-v{new_version}"

    # Guard 3: tag must not exist anywhere. Fetch first so a stale
    # local view of remote tags doesn't let us collide.
    git("fetch", "--tags", "--quiet", capture=False)
    if git("tag", "--list", tag):
        die(f"tag `{tag}` already exists locally — aborting.")
    # `ls-remote` returns empty stdout when the ref is absent, so
    # presence-of-output is the existence check.
    remote_ref = git("ls-remote", "--tags", "origin", tag)
    if remote_ref:
        die(f"tag `{tag}` already exists on origin — aborting.")

    # Write the bumped lakefile. Substitute only the first match
    # (paranoia; there should only be one anyway).
    new_text = VERSION_RE.sub(
        lambda m: f"{m[1]}{new_version}{m[5]}",
        text,
        count=1,
    )
    LAKEFILE.write_text(new_text)
    print(f"bumped lakefile.toml: {major}.{minor}.{patch} → {new_version}")

    # Commit + tag. Letting git output stream through (capture=False)
    # gives the maintainer the usual confirmation lines from each
    # command.
    git("add", str(LAKEFILE), capture=False)
    git(
        "commit",
        "-m",
        f"LeanSha256: bump patch version to {new_version}",
        capture=False,
    )
    git(
        "tag",
        "-a",
        tag,
        "-m",
        f"LeanSha256 v{new_version}",
        capture=False,
    )

    print()
    print("Local commit + tag created. To publish:")
    print(f"  git push origin {branch}")
    print(f"  git push origin {tag}")
    print()
    print(
        "The mirror workflow will translate the tag to "
        f"`v{new_version}` on github.com/etheorem/LeanSha256."
    )


if __name__ == "__main__":
    main()

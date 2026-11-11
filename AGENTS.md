# AGENTS.md

Working agreement for every agent (and human) touching this repo.

## Remote discipline

- **Never leave work only in the local tree.** A green milestone
  (`./tools/check-all.sh` exit 0, or the subproject's own
  `tools/check.sh`) means: commit and push to a remote branch —
  immediately, not "later".
- **Push frequently.** Small, named pushes beat big-bang pushes.
  Unfinished experiments belong on clearly named `wip/…` remote
  branches, not in a dirty working tree or a local-only branch.
- **Open a PR as soon as the work is reviewable**, not when it is
  perfect; keep pushing to the PR branch as it evolves. Merges to
  `main` require one approving review (branch protection enforces
  this). If you lack rights to merge, say so in the PR.
- Credentials: git and curl read `~/.netrc` themselves. Never read,
  copy, print, or commit credential files; never disable branch
  protection to work around a review requirement.

## Before you push

Run the relevant check and let it gate the push:

    ./tools/check-all.sh        # everything
    specs/tools/check.sh        # Lean specs only
    verus/lookup-walk/check.sh  # Verus proof only

Green means exit 0. If your change is mid-flight and the gate is
red, push to a `wip/…` branch with the failure named in the message.
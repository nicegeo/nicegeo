While the class is in session (until May 2026), we will generally only accept contributions from students or auditors in the UIUC class CS 598 TLR Build Your Own Proof Assistant. Any exceptions will be approved by Talia Ringer. 

## Legal
By contributing to this project, you agree that your code is licensed under the license specified in the LICENSE file. 

## Workflow
When working on an issue, please assign yourself to the issue and move the issue to "In Progress" in the project dashboard (can be done on the right side of the issue page). 

Do not push directly to main; work on an appropriately named branch and submit PRs (pull requests) instead. 

Try to separate individual features into individual PRs, rather than combining everything into a single large PR. 
If a feature Y depends on another unimplemented feature X:
- ensure feature X has a branch (and ideally a PR)
- create another branch based on feature X's branch for feature Y (and ideally a draft PR)
- ensure feature X is merged before feature Y
- run `git merge main` in feature Y's branch (optional; GitHub will generally deal with this automatically when making PRs)
- remove the draft status from the PR for feature Y

Don't squash commits when merging; it is easier to track changes this way. Prefer to commit more often rather than less often on feature branches.

The PRs should pass CI, be formatted properly and sufficiently documented, and have at least one approving review with all comments resolved before merging. 

Once a PR is merged, please delete the corresponding feature branch. Create a new branch for any continuations based on the merged main (which will contain another merge commit). 

## AI Usage
Do not use LLMs for the kernel. AI may be used outside the kernel, but you must disclose the scope of any usage of AI tools (i.e. which functions AI was used for, and how it was used) in the PR or commit messages.

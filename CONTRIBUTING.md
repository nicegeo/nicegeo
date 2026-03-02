While the class is in session (until May 2026), we will generally only accept contributions from students or auditors in the UIUC class CS 598 TLR Build Your Own Proof Assistant. Any exceptions will be approved by Talia Ringer. 

## Legal
By contributing to this project, you agree that your code is licensed under the license specified in the LICENSE file. 

## Workflow
When working on an issue, please assign yourself to the issue and move the issue to "In Progress" in the project dashboard (can be done on the right side of the issue page). 

Do not push directly to main; submit PRs instead. The PRs should pass CI, be formatted and documented with ODoc, and have at least one approving review before merging. 

Try to separate individual features into individual PRs, rather than combining everything into a single large PR. 

If there are features that depend on other ones, e.g. feature Y depends on feature X, 
- create a branch and make a PR for feature X
- create another branch based on feature X's branch for feature Y
- create a PR with the base as feature X's branch. 
- Feature X's branch should be merged before feature Y's PR, at which point the base for feature Y's PR can be switched to main.

It is preferred to not squash commits when merging; it is easier to track changes this way. It is better to commit more often rather than less often on feature branches.

## AI Usage
Do not use AI for the kernel. AI may be used outside the kernel, but you must disclose the scope of any usage of AI tools (i.e. which functions AI was used for, and how it was used.)

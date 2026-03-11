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

## Programming Style and Conventions
When working on this project, please adhere to the [OCaml Programming Guidelines](https://ocaml.org/docs/guidelines)

In particular, pay special attention to the following standards:

### ALWAYS add an .mli file for each .ml file
Adding .mli files helps to document which functions are meant to be used in other modules, and which are internal to the module.

### ALWAYS annotate function parameters with types
Annotating the types of function parameters helps the type checker catch cases where the written function doesn't align with the intended function.

### ALWAYS use `snake_case` for lowercase names (not `camelCase`)
Using only one case throughout the code base increases coherence and readability, and `snake_case` is standard in OCaml. `PascalCase` is correct for variants and exceptions, but `Upper_snake_case` should be used for module names.

### PREFER records over tuples
Records provide a baseline level of documentation on the meanings of their fields, while tuples do not.

### AVOID mutual recursion
While mutual recursion is sometimes necessary, it can also make code more difficult to understand and modify, so it should be avoided when possible.

## AI Usage
Do not use LLMs for writing kernel code. However, you may use AI to "red-team" and find kernel bugs, as long as the fixes are human. AI may be used for code outside the kernel, but you must disclose the scope of any usage of AI tools (i.e. which functions AI was used for, and how it was used) in the PR or commit messages. 

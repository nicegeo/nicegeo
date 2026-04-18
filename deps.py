#!/usr/bin/env python3
"""
Build a theorem-only dependency graph for proof.ncg.
A theorem A depends on theorem B if B appears as an identifier in A's proof body.
Definitions and axioms are ignored in the graph.
"""

import re
from collections import defaultdict

NCG_FILE = "proof.ncg"

# Theorem names that are technically valid dependencies but mostly proof plumbing.
IGNORE_THEOREMS = {
    "And.elim1",
    "Eq.symm",
    "EqTrans",
    "Ne.symm",
    "have",
    "fst",
    "snd",
    "and_elim_3",
}

# ---------------------------------------------------------------------------
# 1. Lex all top-level declarations
# ---------------------------------------------------------------------------

DECL_RE = re.compile(r'^(Theorem|Definition|Axiom)\s+(\S+)', re.MULTILINE)


def parse_declarations(text):
    """Return list of dicts: kind, name, body_text."""
    matches = list(DECL_RE.finditer(text))
    decls = []
    for i, m in enumerate(matches):
        kind = m.group(1)
        name = m.group(2)
        start = m.start()
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        chunk = text[start:end]
        # Body is everything after the first :=
        assign = chunk.find(':=')
        body = chunk[assign + 2:] if assign >= 0 else ''
        decls.append({'kind': kind, 'name': name, 'body': body})
    return decls


# ---------------------------------------------------------------------------
# 2. Build dependency graph
# ---------------------------------------------------------------------------

def build_graph(decls):
    """
    Returns:
      deps  : dict[str, set[str]]  — direct deps for each theorem
      proved: set[str]             — theorems with actual proofs (no sorry)
      todos : set[str]             — theorems with sorry _ (* TODO *)
    """
    theorem_names = {
        d['name']
        for d in decls
        if d['kind'] == 'Theorem' and d['name'] not in IGNORE_THEOREMS
    }

    todos = set()
    proved = set()

    deps = {}
    for d in decls:
        if d['kind'] != 'Theorem':
            continue
        name = d['name']
        body = d['body']

        if name in IGNORE_THEOREMS:
            continue

        # Classify
        if 'sorry _' in body and '(* TODO *)' in body:
            todos.add(name)
        else:
            proved.add(name)

        # Find references to other theorems only
        found = set()
        for other in theorem_names:
            if other == name:
                continue
            if re.search(r'(?<![A-Za-z0-9_])' + re.escape(other) + r'(?![A-Za-z0-9_])', body):
                found.add(other)

        deps[name] = found

    return deps, proved, todos


# ---------------------------------------------------------------------------
# 3. Transitive closure helpers
# ---------------------------------------------------------------------------

def transitive_deps(name, deps, cache=None):
    if cache is None:
        cache = {}
    if name in cache:
        return cache[name]
    visited = set()
    stack = list(deps.get(name, []))
    while stack:
        n = stack.pop()
        if n in visited:
            continue
        visited.add(n)
        for m in deps.get(n, []):
            if m not in visited:
                stack.append(m)
    cache[name] = visited
    return visited


def reverse_graph(deps):
    rev = defaultdict(set)
    for node, nbrs in deps.items():
        for nbr in nbrs:
            rev[nbr].add(node)
    return dict(rev)


# ---------------------------------------------------------------------------
# 4. Main
# ---------------------------------------------------------------------------

def main():
    with open(NCG_FILE) as f:
        text = f.read()

    decls = parse_declarations(text)
    deps, proved, todos = build_graph(decls)
    rev = reverse_graph(deps)

    all_thms = sorted(proved | todos)

    # --- print direct deps for every theorem ---
    print("=" * 70)
    print("DIRECT THEOREM DEPENDENCIES")
    print("=" * 70)
    for name in all_thms:
        d = sorted(deps.get(name, []))
        status = "TODO" if name in todos else "ok"
        print(f"\n[{status}] {name}")
        if d:
            for dep in d:
                dep_status = "TODO" if dep in todos else "ok"
                print(f"      uses [{dep_status}] {dep}")
        else:
            print("      (no theorem deps)")

    # --- which proved-set theorems are needed by square_of_len transitively ---
    print("\n" + "=" * 70)
    print("TRANSITIVE DEPS OF square_of_len")
    print("=" * 70)
    sq_deps = transitive_deps('square_of_len', deps)
    sq_todo = sorted(sq_deps & todos)
    sq_ok   = sorted(sq_deps & proved)
    print(f"\n  Still TODO ({len(sq_todo)}):")
    for n in sq_todo:
        print(f"    {n}")
    print(f"\n  Already proved ({len(sq_ok)}):")
    for n in sq_ok:
        print(f"    {n}")

    # --- what does each TODO block (reverse deps) ---
    print("\n" + "=" * 70)
    print("REVERSE DEPS: which theorems are blocked by each TODO")
    print("=" * 70)
    for name in sorted(todos):
        blocked = sorted(rev.get(name, []))
        print(f"\n  {name}")
        if blocked:
            for b in blocked:
                print(f"    ← {b}")
        else:
            print("    (nothing directly depends on it)")


if __name__ == '__main__':
    main()

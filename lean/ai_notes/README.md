# ai_notes

Technical notes of the Lean formalization in `lean/`, written by Claude during the proving runs.
Nothing in `SkipsLean/` reads them, and the index of the library itself is `lean/STATEMENTS.md`.

- `lean-status-by-statement-2026-11-24.md`: every numbered statement of the three papers, with its
  status and the Lean file that holds it. Start here.
- `lean-statement-audit-*.md`: the reports of the readers who compared the Lean statements with the
  papers, statement by statement.
- `lean-remarks-on-proofs-2026-11-23.md`: remarks on the papers' proofs, found while formalizing them.
- `*_check_*.py` with their outputs `*.out`: numeric checks of statements, run before they were
  stated in Lean.
- `lean-AGENTS.md`, `lean-ERRORS.md`: the rules for the proving agents, and the log of compile errors
  with their fixes. Their working copies in `lean/` are ignored by git.
- `axioms-check-latest.out`: the output of `lake env lean checks/Axioms.lean` after the last full
  build.

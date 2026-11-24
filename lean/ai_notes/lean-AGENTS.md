# Rules for an agent working in this repository

This folder (`lean/` of the repository `skips_fix_gauges`) formalizes, in Lean 4 with Mathlib,
statements of the papers "On the Functional Dimension of a Family of Analytic Neural Networks" and
"Skip Connections Unlock at Least d_model² Parameters per Layer". Read `STATEMENTS.md` first.

All paths below are relative to this `lean/` folder, and every `lake` command is run from it. The
three files `AGENTS.md`, `PROGRESS.md` and `ERRORS.md` are working notes: they are not tracked by
git (see `.gitignore`), so `git add -A` does not commit them. Edit `PROGRESS.md` and `ERRORS.md` in
place in your worktree; the coordinator collects them. Do not touch anything of the repository
outside `lean/` (the papers, the notebooks, the scripts).

1. **You prove; you do not restate.** The definitions and the statements of the theorems are
   fixed. Do not change a definition, a theorem statement, a hypothesis, or a file other than the
   one you were given. You may add private helper lemmas to your file, above the theorem that
   uses them.
2. **If a statement looks false or cannot be proved as written, stop** and report the smallest
   counterexample or the exact obstacle (the goal state you cannot close, and why). Do not weaken
   the statement, do not add a hypothesis, do not use `sorry`, `admit`, `native_decide`, a new
   `axiom`, or `unsafe` code to get past it.
3. **Done means compiled.** Run `export PATH="$HOME/.elan/bin:$PATH"` and then
   `lake build <Module>` (for example `lake build SkipsLean.Basic.RMSNorm`). A lemma is proved only
   when the build of its file passes and the file contains no `sorry` in that lemma. Never report
   a proof that you did not compile. Never run `lake update`, `lake clean`, or change
   `lakefile.toml`, `lean-toolchain` or `lake-manifest.json`.
4. **Commit each state of your file that compiles**, from the root of your worktree:
   `git add lean && git commit -q -m "lean: <file>: prove <lemma(s)>"`. One commit may hold several
   lemmas. Never rebuild only to split a commit by lemma: a build is the expensive step here.
   Use the default git identity of the session (the commits are then signed); do not pass
   `-c user.name` or `-c user.email`, and add no attribution lines to the message. Never push.
5. **After every commit, append an entry to `PROGRESS.md`** (it is not tracked by git, so there is
   nothing to commit for it): the lemma, its status (proved / proved with helper `<name>` / blocked), the Mathlib
   lemmas the proof relies on, what you tried that failed, and what the next run should start with.
6. Scratch files go in `scratch/` at the root of your worktree (it is in `.gitignore`); compile one
   with `lake env lean scratch/Foo.lean`. To find Mathlib lemmas, search the sources under `.lake/packages/mathlib/Mathlib/` with grep,
   and use `exact?`, `apply?`, `rw?`, `simp?` in a scratch file. Mathlib is pinned to `v4.36.0`;
   names may differ from what you remember, so check before you rely on a name.
7. Keep proofs readable: short tactic blocks, a comment for each mathematical step that mirrors
   the paper's proof, no `simp` without `only` at the end of a long proof if `simp?` gives a
   stable list.
8. At the end, add `#print axioms <theorem>` for each main theorem in a scratch file (not in the
   repository), and report its output: only `propext`, `Classical.choice`, `Quot.sound` may appear.
9. **Errors worth remembering go to `ERRORS.md`.** Read that file before you start. When an
   error cost you more than one build round and its fix could help someone else, add an entry of
   at most 4 lines (Error, Cause, Fix, Where) under the fitting heading, after checking that it
   is not there already. Keep it short: no goal dumps, no proof scripts. The file has a cap of
   150 lines.
10. **The machine can restart at any time**, and a restart stops you without warning. What is on
    disk survives; what is only in your head does not. Commit as soon as one lemma compiles in the
    real file, keep a draft in `scratch/` while you work on a long proof, and write `PROGRESS.md`
    entries as you go, not at the end.
11. **Builds are the bottleneck: spend them with care.** The machine has 2 cores and 8 GB, and
    other agents compile at the same time. (a) Develop a proof in a scratch file with SHORT imports
    (the few Mathlib modules it needs, or `import SkipsLean.Imports` once that file exists), not
    `import Mathlib`: loading all of Mathlib takes from 20 seconds to 2 minutes per compile,
    depending on the load. (b) Check your real file with `lake env lean SkipsLean/<Your/File>.lean`
    while you work (it needs no build of other modules), and run `lake build <YourModule>` once,
    when the file is finished. (c) Start a compile in the background and write the next proof
    while it runs; never sit idle on a build. (d) Never build the whole library, and never build a
    module other than yours.
12. **Show your progress at least every 10 minutes.** A long proof is developed in scratch, and from
    outside a scratch file cannot be told from a loop. So: as soon as helpers compile, move them
    into the real file above the theorem (the theorem may stay `sorry`), commit that partial state
    (`lean: <file>: partial, helpers checked`), and append three lines to `PROGRESS.md`: what is
    proved, what is left, what blocks (or "nothing blocks"). Do this at least every 10 minutes. If
    the same step has failed three times, say so in the third line: the coordinator then decides
    whether another agent takes the proof over, from your update and not from the clock.

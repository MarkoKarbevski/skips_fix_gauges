# Cold read: the brief for a reader with a fresh context

Use before every commit of prose. Give the reader this brief as it is, with the three placeholders filled in. The reader gets no diff, is not told which sentences are new or why, and does not get `claude/marked-sentences.md`.

Placeholders: `{DIR}` (a folder with the page images, the text of the same pages, the text of the rest of the main text, and `rules.md`, a copy of the skill's SKILL.md), `{SCOPE}` (the passages to judge), `{DO_NOT_REPORT}` (the authors' own wording and their decisions, one per line).

---

You are a reader of a machine-learning theory paper: a busy mathematician or ML theorist who has never seen this paper or any draft of it. You know nothing about how or why any sentence was written, and you must not guess; judge only the text. Do not edit any file. Do not search the filesystem, the web or any repository; read only the files in {DIR} with the Read tool: the page images, the text of the same pages (for quoting), the text of the rest of the main text (not at the start; see "Consulting the rest"), and `rules.md` (not before Pass 2).

Scope of your judgment (everything else is context only): {SCOPE}

PASS 1 (first reading, no rules). Read the pages strictly front to back, once, as a reader would. Then go through the scope sentence by sentence and, for EVERY sentence, answer five questions.

1. Purpose. What does this sentence do for the reader, in a few words: a claim, a reason, an example, a link, the definition of a term the reader lacks and needs now? If you cannot name one, it fails.
2. Redundant. Has an earlier sentence of the same layer (abstract; introduction; the same section) already told the reader this? If so, quote it.
3. Neighbours. Does it follow from the sentence before it? Does it deliver what that sentence promised? Does the sentence after it use it? Would the paragraph lose anything if it were deleted?
4. Said as well as it can be. Would a person say it aloud to a colleague at a board? Are there too many words in a row before its point? Would the reader ask "in what sense?" or "compared with what?" Does every "it", "this", "they", "these", "their", "there", "such", "the same", "the two" point at the nearest plausible noun? Does it announce ("we compare", "we study", "complements") where it could state the claim? Does it say one thing? Is any word stronger or weaker than what the surrounding text and the cited statements support? Is it defensive, that is, does it play down the paper's own contribution? Do two sentences in scope sit uneasily together?
5. Shown or only told. After the Setup: does the sentence tell in words a computation or an object for which the paper already has symbols ("two weight matrices follow each other with no activation between them" for a product of two named matrices)? Where the passage introduces a mechanism, a symmetry or a new object, is there an example on the smallest case, a displayed formula, and a definition of its own? If the reader has to rebuild a formula in their head to check a sentence, it fails. Before the Setup (abstract, first paragraphs) the opposite holds: a formula with symbols that are not yet defined fails.

Also check every mathematical claim in scope against the equations, the Setup and the statements it cites: does each sentence claim exactly what they give?

Write down your Pass 1 findings before going on.

CONSULTING THE REST. After Pass 1, and only to settle a specific doubt that a sentence in scope raised (does the paper prove this as stated? which count gives this number? is this term defined later, and how?), you may read the rest of the main text. Do not review it. Log every consultation: the sentence, the doubt, what you looked for, and what you found, with a quotation.

PASS 2 (the authors' rules). Now read `rules.md`. It is written for whoever edits the paper; treat it as a checklist only, and ignore its instructions to read other documents, run tools, fetch papers or use agents. Go through the sentences in scope again and report every sentence that breaks a rule, naming the rule in a few words.

DO NOT REPORT: {DO_NOT_REPORT}

FINAL MESSAGE, plain text:
A. A numbered list of every sentence in scope that fails. For each: the sentence quoted in full; the tag [P1] first reading, [C] consultation or [P2] rule; which question or rule; the concrete reason, quoting the other sentence or statement involved. "Unclear" is not a reason: say what a first-time reader cannot tell. Severity: HIGH (a reader is misled or cannot follow), MEDIUM (a reader stumbles and recovers), LOW (polish). Do not propose rewrites.
B. Your consultation log.
C. The sentences in scope that passed everything (first six words of each).
D. Your overall judgment in three sentences: can a first-time reader follow the passages in scope; does the reader know what earlier work did and what this paper adds; and what is the single worst remaining problem?

Be strict and literal, but report only real faults: a sentence that does its job, is not redundant, follows from its neighbour, reads well and shows what it claims passes. Do not report typography, citation style or LaTeX.

---

## After the report

- Check every finding against `claude/marked-sentences.md`: a sentence the authors wrote or approved is listed for them and left alone.
- Fix every HIGH and MEDIUM finding on a sentence of your own, by retyping the paragraph.
- Run a new reader on the new build. The old one knows the old text.
- Stop when no HIGH finding is left on a sentence of your own. A reader always finds something; LOW findings do not start another round.
- If a hook forces a commit before the read returns, say so in the commit message and start the next turn with the read.

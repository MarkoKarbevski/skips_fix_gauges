# Novelty checks

Is the gauge view of skip connections common knowledge? On 2026-11-05, four AI models were asked the same question,
without web search:

> Why do skip connections improve neural networks? Give me all the reasons.
>
> Provide a long elaborate answer. No online searching.

None of the four answers mentions a change of basis at the hidden states, the dimensions of symmetry that the skips
remove, or functional dimension. Their reasons concern optimization (gradient paths, conditioning, the loss
landscape), information flow, implicit ensembles, the ODE view and engineering.

| File | Model | Shared conversation |
|---|---|---|
| `2026-11-05_claude-opus-5.5-max.txt` | Claude Opus 5.5, max effort | https://claude.ai/share/95d519cb-c625-4a1f-b5fc-3ce401d8ee0e |
| `2026-11-05_chatgpt-thinking.txt` | ChatGPT with Thinking | https://chatgpt.com/share/6aecc96c-1564-83ed-af1e-4eddd0583b26 |
| `2026-11-05_argon-high.txt` | Argon High | https://share.gemini.google/q0p5GHixoOd6 |
| `2026-11-05_deepseek-deepthink.txt` | DeepSeek with DeepThink | https://chat.deepseek.com/share/vn2h67p6ccbi42z3z2 |

The files are verbatim copies of the answers as copied from the chat interfaces. Formulas appear as copied, often
twice because of the math rendering. The DeepSeek file includes its visible thinking. The ChatGPT file contains the
captions of a few images that its interface inserted, and its closing upgrade notice. `SHA256SUMS` holds the hash of
each file, and the commit that adds them dates them.

## The closest statements

- **ChatGPT**: "at a fixed block architecture and width, the residual structure can make certain transformations
  available that a plain block cannot represent without additional resources", with the example that "a
  one-hidden-layer ReLU MLP may need additional units to represent the identity function itself"; and "Parameter
  count and functional capacity are not the same thing."
- **Claude**: "A conv–BN–ReLU stack can express the identity (x = ReLU(x) − ReLU(−x)), but only with finely
  coordinated weights"; an identity skip breaks the symmetry between interchangeable hidden units (after Orhan and
  Pitkow, 2018); and "the main effect is on optimization, not on what a network can represent."
- **Argon High**: skip connections "break the structural symmetries of the weight space" that create degenerate
  manifolds (after Orhan and Pitkow, 2018), and a plain layer spends "a large fraction of its parameters learning
  identity subspaces."
- **DeepSeek**: a residual block "can represent essentially the same class of functions as a plain block if F is
  expressive enough". Theorem 3.4 of the note (`thm:noabsorb`) shows that at equal width this fails for generic
  weights.

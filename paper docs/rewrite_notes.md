# Editorial notes for the skip-connection papers

## Keep the two introductions distinct

The absorption paper introduces exact replacement. It asks whether a skipless block or network can reproduce a particular residual function and what extra width the replacement requires.

The functional-dimension paper follows that result. Cite Mijoski and Karbevski in the first paragraph, then name the quantity the earlier work leaves open. How much do identity skips change functional dimension when the blocks and parameter count are fixed?

## Show the step that makes the conclusion follow

| Draft problem | What the reader needs |
| --- | --- |
| “Changing the coordinates of a hidden state can be undone by the next block's input weights.” | Name both operations. The preceding block's output weights write the state in the new basis. The next block's input weights apply the inverse change. Say that the network function is preserved. |
| “An identity skip adds that state … tying the coordinates on either side of the block.” | Name the input and output states and explain the constraint. A skip has no trainable matrix to convert from one basis to the other. If the basis changes differ, the transformed skip is a conversion matrix. It remains the identity only when the two changes agree. |
| “The resulting rank constraint yields the width lower bound.” | Identify the rank being compared and explain what one added unit contributes. Link the argument to the full-rank identity skip and keep the genericity qualification. |
| “The discrepancy is analytic … Part (ii) strengthens this to a uniform lower bound.” | Keep the quantifiers visible. For each candidate block there is an input on which it differs from the target. The error bound is independent of the candidate, while the input that witnesses it can depend on the candidate. |
| “The same calculation gives a lower bound on the gain.” | Explain which network attains its bound and which may fall below its bound. Subtracting the skipless upper bound from the attained residual dimension gives the guaranteed gain. |

## Check the prose in reading order

- Open with the scientific question or the result that motivates it. Put routine architecture definitions where the reader first needs them.
- Name the object when the argument changes scale. A junction between blocks, the endpoints of one block, and the whole network are three different scopes.
- Give “this,” “that,” and “it” a clear antecedent. If a paragraph introduces two networks or several matrices, repeat the relevant name where needed.
- Keep assumptions beside the claims they qualify. Check which block types, normalization, widths, and quantifiers apply.
- Separate exact equality from approximation, and parameter-count bounds from attained functional dimension.
- Give each paragraph one job. A short summary earns its place when it helps the reader anticipate the argument. If the next paragraph repeats the same point with the missing mechanism, combine them.

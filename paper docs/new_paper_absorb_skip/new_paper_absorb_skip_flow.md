# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | ReLU squared, d_model, the dimension, gated block, readout / unembedding | d_model, the dimension, gated block, generic / almost every, readout / unembedding, residual, skipless | \begin{abstract} Residual networks add each block's input to its outpu |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para |  |  | Almost every deep network trained today adds the input of a block to i |
| 3 | Introduction | para |  |  | Skipless networks now train too. \citet{he2024simplifying} remove the  |
| 4 | Introduction | para | H and d_h, absorb, m, number of units | H and d_h, absorb, attention block, m, number of units | We answer this question block by block. Take an MLP block $B$ with $m$ |
| 5 | Introduction | para |  | ReLU squared | \para{Without biases, the answer depends on the activation.} \begin{it |
| 6 | Introduction | para | t and u, a ray | t and u, a ray | \para{Four one-line reasons.} Follow the input along a ray, $x = tu$ w |
| 7 | Introduction | para | RMSNorm and its epsilon, pre-RMSNorm | RMSNorm and its epsilon, pre-RMSNorm | \para{Networks.} Throughout, a network starts with a linear embedding  |
| 8 | Introduction | para |  |  | \para{No function lost in the limit.} Without normalization, every ski |
| 9 | Introduction | float |  |  | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.12} \ |
| 10 | Setup | para |  |  | \section{Setup}\label{sec:setup} \takeaway{One equation states the que |
| 11 | Setup | para | B_theta, Wread, Wwrite, theta, T, number of tokens, read / write (nouns) | B_theta, Wread, Wwrite, theta, T, number of tokens, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 12 | Setup | para | M, the linear term | M, the linear term | \para{The question as an equation.} A skip adds $x$ to the output of a |
| 13 | Setup | para | E and D, L, the number of blocks, N(h), X, the input of a network, residual, skipless | E and D, L, the number of blocks, N(h), X, the input of a network | \para{Networks.} Every network starts with a linear embedding $E \in \ |
| 14 | Setup | para | generic / almost every |  | \para{Scope.} Blocks have no biases, and the answers depend on it. Wit |
| 15 | One block | para |  |  | \section{One block}\label{sec:oneblock} \takeaway{For almost every ReL |
| 16 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | \subsection{ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm |
| 17 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | mirror image | mirror image | Both activations satisfy \begin{equation}\label{eq:odd} \sigma(z) - \s |
| 18 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | w_i and hat w_i, read and write of a unit, with more units. | w_i and hat w_i, read and write of a unit, with more units. | \emph{With more units.} Let unit $i$ have read $w_i$, a column of $\Wr |
| 19 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | S, a set of units, at the same width. | S, a set of units, at the same width. | \emph{At the same width.} Flipping the read of unit $i$ to $-w_i$ chan |
| 20 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | nondegenerate | nondegenerate | The next theorem says that these are the only ways. A block is \emph{n |
| 21 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[ReLU and GELU blocks]{theorem}{thmAbsorbReLU}\label |
| 22 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | In (i), generic weights give no set of units with the required product |
| 23 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | The proof matches the units of the two blocks. The even part of the ac |
| 24 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | \para{Networks of one block.} A network of one block computes $X \maps |
| 25 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[Networks of one block]{proposition}{propOneBlockNet |
| 26 | ReLU\texorpdfstring{$^2$ | para |  |  | \subsection{ReLU\texorpdfstring{$^2$}{2}, gated and tanh blocks}\label |
| 27 | ReLU\texorpdfstring{$^2$ | para |  |  | \begin{figure}[t] \centering |
| 28 | ReLU\texorpdfstring{$^2$ | float |  |  | \caption{Why no width absorbs the skip. Along a ray $x = tu$ the skip  |
| 29 | ReLU\texorpdfstring{$^2$ | para |  |  | Recall that a block absorbs $xM$ if a block of the same kind satisfies |
| 30 | ReLU\texorpdfstring{$^2$ | statement |  |  | \begin{restatable}[No width suffices]{theorem}{thmAbsorbHom}\label{thm |
| 31 | ReLU\texorpdfstring{$^2$ | para |  |  | The three cases of \cref{fig:reasons} are three one-line proofs. A hom |
| 32 | Attention blocks | para |  |  | \subsection{Attention blocks}\label{sec:attention} |
| 33 | Attention blocks | para | Gamma, attention scores, attention block, score matrix, value-output product | Gamma, attention scores, score matrix, value-output product | An \emph{attention block} with parameters $\theta = (W_{Q,i}, W_{K,i}, |
| 34 | Attention blocks | para |  |  | Attention mixes tokens, and a skip keeps each token where it is. Suppo |
| 35 | Attention blocks | statement |  |  | \begin{restatable}[Attention blocks]{theorem}{thmAttention}\label{thm: |
| 36 | Attention blocks | para |  |  | The proof gives a gap: on some input with rows of norm at most $1$, on |
| 37 | Networks | para |  |  | \section{Networks}\label{sec:networks} \takeaway{Between an embedding  |
| 38 | Networks | para |  |  | Recall that a network embeds its input as $h_0 = XE$ and reads out $y  |
| 39 | Networks | statement |  |  | \begin{restatable}[Networks that never absorb their skips]{theorem}{th |
| 40 | Networks | para |  |  | With $E = D = I$, this covers compositions of blocks. The reasons are  |
| 41 | Networks | para |  |  | \para{ReLU networks need a wide first block.} |
| 42 | Networks | statement |  |  | \begin{restatable}[ReLU networks]{theorem}{thmAbsorbFirst}\label{thm:r |
| 43 | Networks | para |  |  | The proof compares ranks. Near almost every input, a generic residual  |
| 44 | Networks | para |  |  | Conversely, the construction of \cref{sec:relugelu} works block by blo |
| 45 | Networks | statement |  |  | \begin{restatable}[Extra units]{proposition}{propExtraUnits}\label{pro |
| 46 | Networks | para |  |  | So $L\dm$ extra units in all suffice; for ReLU, the first block needs  |
| 47 | Networks | para |  |  | \para{RMSNorm with $\varepsilon = 0$: the skip keeps the length of the |
| 48 | Networks | statement | F, the function of a network | F, the function of a network | \begin{restatable}[Absorption under RMSNorm with $\varepsilon = 0$]{pr |
| 49 | Networks | para |  |  | For (ii), let $c \to \infty$: the blocks read $N(h)$, whose rows have  |
| 50 | Skipless networks are limits of residual ones | para |  |  | \section{Skipless networks are limits of residual ones}\label{sec:limi |
| 51 | Skipless networks are limits of residual ones | statement |  |  | \begin{restatable}[Skipless networks as limits of residual networks]{p |
| 52 | Skipless networks are limits of residual ones | para |  |  | \para{Blocks that outweigh their skips.} The proof scales the reads of |
| 53 | Skipless networks are limits of residual ones | para |  |  | \para{Under RMSNorm.} With $\varepsilon = 0$, RMSNorm ignores the size |
| 54 | Related work | para |  |  | \section{Related work}\label{sec:related} |
| 55 | Related work | para |  |  | \para{Expressivity of residual networks.} \citet{lin2018resnet} show t |
| 56 | Related work | para |  |  | \para{Identifiability.} For $\tanh$ networks, the function determines  |
| 57 | Related work | para |  |  | \para{Training without skips.} Skipless networks train with careful in |
| 58 | Conclusion | para |  |  | \section{Conclusion}\label{sec:conclusion} |
| 59 | Conclusion | para |  |  | Can a skip let a block compute a function that no skipless block of th |
| 60 | Conclusion | para |  |  | \para{Open questions.} The dashes of \cref{tab:results} leave three qu |
| 61 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 62 | Use of AI | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

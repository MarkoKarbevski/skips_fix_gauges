# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | ReLU squared, absorb, d_model, the dimension, gated block | RMSNorm, absorb, d_model, the dimension, gated block, generic / almost every, residual, skipless | \begin{abstract} Residual networks add each block's input to its outpu |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para |  |  | Almost every deep network trained today, from residual networks \citep |
| 3 | Introduction | para |  |  | Skipless networks now train too. \citet{he2024simplifying} remove the  |
| 4 | Introduction | para | B, the map of a block, H and d_h, m, number of units | B, the map of a block, H and d_h, attention block, m, number of units | We answer this question block by block. Take an MLP block $B$ with $m$ |
| 5 | Introduction | para |  | ReLU squared, mirror image | \para{Without biases, the answer depends on the activation.} \begin{it |
| 6 | Introduction | para | t and u, a ray | t and u, a ray | \para{Four one-line reasons.} Follow the input along a ray, $x = tu$ w |
| 7 | Introduction | para | RMSNorm, epsilon of RMSNorm, pre-RMSNorm, readout / unembedding | epsilon of RMSNorm, pre-RMSNorm, readout / unembedding | \para{Networks.} Throughout, a network starts with a linear embedding  |
| 8 | Introduction | para |  |  | \para{No function lost in the limit.} Without normalization, every ski |
| 9 | Introduction | float | with pre-rmsnorm: | with pre-rmsnorm: | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.12} \ |
| 10 | Setup | para |  |  | \section{Setup}\label{sec:setup} \takeaway{One equation states the que |
| 11 | Setup | para | B_theta, Wread, Wwrite, theta, T, number of tokens, read / write (nouns) | B_theta, Wread, Wwrite, theta, T, number of tokens, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 12 | Setup | para | M, the linear term | M, the linear term | \para{The question as an equation.} A skip adds $x$ to the output of a |
| 13 | Setup | para | E and D, L, the number of blocks, N(h), X, the input of a network, residual, skipless | E and D, L, the number of blocks, N(h), X, the input of a network | \para{Networks.} A network maps an input $X \in \R^{T\times d_{\mathrm |
| 14 | Setup | para |  |  | \para{No biases.} Blocks have no biases, and the answers depend on it. |
| 15 | Setup | para | generic / almost every |  | \para{Scope.} Every MLP block has at least $\dm$ hidden units, so that |
| 16 | One block | para |  |  | \section{One block}\label{sec:oneblock} \takeaway{For almost every ReL |
| 17 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | \subsection{ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm |
| 18 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | mirror image |  | Both activations satisfy \begin{equation}\label{eq:odd} \sigma(z) - \s |
| 19 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | w_i and hat w_i, read and write of a unit, with more units. | w_i and hat w_i, read and write of a unit, with more units. | \emph{With more units.} Let unit $i$ have read $w_i$, a column of $\Wr |
| 20 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | S, a set of units, at the same width. | S, a set of units, at the same width. | \emph{At the same width.} Flipping the read of unit $i$ to $-w_i$ chan |
| 21 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | nondegenerate | nondegenerate | The next theorem says that at the same width these flips are the only  |
| 22 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[ReLU and GELU blocks]{theorem}{thmAbsorbReLU}\label |
| 23 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | In (i), for each of the finitely many sets $S$, the equation $\Wread[{ |
| 24 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | The proof matches the units of the two blocks. The even part of the ac |
| 25 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | \para{Networks of one block.} A residual network of one block is a blo |
| 26 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[Networks of one block]{proposition}{propOneBlockNet |
| 27 | ReLU\texorpdfstring{$^2$ | para |  |  | \subsection{ReLU\texorpdfstring{$^2$}{2}, gated and \texorpdfstring{$\ |
| 28 | ReLU\texorpdfstring{$^2$ | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 29 | ReLU\texorpdfstring{$^2$ | para |  |  | Recall that a block absorbs $xM$ if a block of the same kind satisfies |
| 30 | ReLU\texorpdfstring{$^2$ | statement |  |  | \begin{restatable}[No width suffices]{theorem}{thmAbsorbHom}\label{thm |
| 31 | ReLU\texorpdfstring{$^2$ | para |  |  | The three cases of \cref{fig:reasons} are three one-line proofs. A hom |
| 32 | Attention blocks | para |  |  | \subsection{Attention blocks}\label{sec:attention} |
| 33 | Attention blocks | para | Gamma, attention scores, attention block, score matrix, value-output product | Gamma, attention scores, score matrix, value-output product | An \emph{attention block} with parameters $\theta = (W_{Q,i}, W_{K,i}, |
| 34 | Attention blocks | para |  |  | Attention mixes tokens, and a skip keeps each token where it is. Suppo |
| 35 | Attention blocks | statement |  |  | \begin{restatable}[Attention blocks]{theorem}{thmAttention}\label{thm: |
| 36 | Attention blocks | para |  |  | The same two inputs show that a residual network of one attention bloc |
| 37 | Networks | para |  |  | \section{Networks}\label{sec:networks} \takeaway{Between an embedding  |
| 38 | Networks | para |  |  | Recall that a network embeds its input as $h_0 = XE$ and reads out $y  |
| 39 | Networks | statement |  |  | \begin{restatable}[Networks that never absorb their skips]{theorem}{th |
| 40 | Networks | para |  |  | With $E = D = I$, this covers compositions of blocks. The reasons are  |
| 41 | Networks | para |  |  | \para{ReLU and GELU networks need a wide first block.} |
| 42 | Networks | statement |  |  | \begin{restatable}[ReLU and GELU networks]{theorem}{thmAbsorbFirst}\la |
| 43 | Networks | para |  |  | For ReLU the proof compares ranks. Near almost every input, a generic  |
| 44 | Networks | para |  |  | Conversely, the construction of \cref{sec:relugelu} works block by blo |
| 45 | Networks | statement |  |  | \begin{restatable}[Extra units]{proposition}{propExtraUnits}\label{pro |
| 46 | Networks | para | contraction | contraction | So $\dm$ extra units per block suffice, and the first block of a skipl |
| 47 | Networks | statement |  |  | \begin{restatable}[Contractive blocks]{proposition}{propEveryBlock}\la |
| 48 | Networks | para |  |  | This condition holds on an open set of weights, which contains every n |
| 49 | Networks | para |  |  | \para{RMSNorm: the skip keeps the norm of each token.} A skipless netw |
| 50 | Networks | statement |  |  | \begin{restatable}[Networks under RMSNorm]{theorem}{thmRMSNet}\label{t |
| 51 | Networks | para |  |  | Scale an input $X$ by a factor $t \to \infty$. A skipless network with |
| 52 | Skipless networks are limits of residual ones | para |  |  | \section{Skipless networks are limits of residual ones}\label{sec:limi |
| 53 | Skipless networks are limits of residual ones | statement | F, the function of a network | F, the function of a network | \begin{restatable}[Skipless networks as limits of residual networks]{p |
| 54 | Skipless networks are limits of residual ones | para |  |  | \para{Blocks that outweigh their skips.} The proof scales the reads of |
| 55 | Skipless networks are limits of residual ones | para |  |  | \para{Under RMSNorm.} With $\varepsilon = 0$, RMSNorm ignores the size |
| 56 | Related work | para |  |  | \section{Related work}\label{sec:related} |
| 57 | Related work | para |  |  | \para{Expressivity of residual networks.} \citet{lin2018resnet} show t |
| 58 | Related work | para |  |  | \para{Identifiability.} For $\tanh$ networks, the function determines  |
| 59 | Related work | para |  |  | \para{Training without skips.} Skipless networks train with careful in |
| 60 | Conclusion | para |  |  | \section{Conclusion}\label{sec:conclusion} |
| 61 | Conclusion | para |  |  | Can a block absorb its skip? Without biases, it depends on the activat |
| 62 | Conclusion | para |  |  | \para{Open questions.} The unknown cells and the conditions of \cref{t |
| 63 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 64 | Use of AI | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

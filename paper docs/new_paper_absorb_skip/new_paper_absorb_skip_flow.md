# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | ReLU squared, absorb, d_model, the dimension, gated block | RMSNorm, absorb, attention block, d_model, the dimension, gated block, generic / almost every, residual, skipless | \begin{abstract} Residual networks add each block's input to its outpu |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para |  |  | Nearly every deep network trained today, from residual networks \citep |
| 3 | Introduction | para |  |  | Skipless networks now train too. \citet{he2024simplifying} remove the  |
| 4 | Introduction | para | B, the map of a block, H and d_h, m, number of units | B, the map of a block, H and d_h, m, number of units | Let $B$ be an MLP block with $m$ hidden units, or an attention block w |
| 5 | Introduction | para |  | ReLU squared | \para{One block: the answer depends on the activation.} \begin{itemize |
| 6 | Introduction | para | t and u, a ray | t and u, a ray | \para{Why the other blocks never absorb.} Along a ray $x = tu$ with $t |
| 7 | Introduction | para | E and D, RMSNorm, X, the input of a network, epsilon of RMSNorm, pre-RMSNorm, readout / unembedding | E and D, X, the input of a network, epsilon of RMSNorm, pre-RMSNorm, readout / unembedding | \para{Networks: the negative answers carry over.} Throughout, a networ |
| 8 | Introduction | para |  |  | \para{Skipless networks as limits.} Without normalization, every skipl |
| 9 | Introduction | para |  |  | \para{Outline.} \Cref{tab:results} collects the results. \Cref{sec:set |
| 10 | Introduction | float | with pre-rmsnorm: | with pre-rmsnorm: | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.12} \ |
| 11 | Setup | para |  |  | \section{Setup}\label{sec:setup} \takeaway{One equation states the que |
| 12 | Setup | para | B_theta, Wread, Wwrite, theta, T, number of tokens, read / write (nouns) | B_theta, Wread, Wwrite, theta, T, number of tokens, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 13 | Setup | para | M, the linear term | M, the linear term | \para{Absorbing a linear term.} A skip adds $x$ to the output of a blo |
| 14 | Setup | para | L, the number of blocks, residual, skipless | L, the number of blocks | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 15 | Setup | para | N(h) | N(h) | \para{Normalization.} RMSNorm, written $N$, divides each row $v$ of a  |
| 16 | Setup | para |  |  | \para{Biases.} Blocks have no biases, and the answers depend on it. Wi |
| 17 | Setup | para |  |  | \para{Scope.} Every MLP block has at least $\dm$ hidden units, so that |
| 18 | Setup | para | generic / almost every |  | \para{Generic weights.} A statement holds for \emph{generic} weights,  |
| 19 | One block | para |  |  | \section{One block}\label{sec:oneblock} \takeaway{For almost every ReL |
| 20 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | \subsection{ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm |
| 21 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | mirror image, w_i and hat w_i, read and write of a unit | mirror image, w_i and hat w_i, read and write of a unit | ReLU and GELU both satisfy \begin{equation}\label{eq:odd} \sigma(z) -  |
| 22 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | with more units. | with more units. | \emph{With more units.} For a row $\gamma \in \R^{1\times\dm}$, a new  |
| 23 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | S, a set of units, at the same width. | S, a set of units, at the same width. | \emph{At the same width.} Flipping the read of unit $i$ to $-w_i$ chan |
| 24 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para | nondegenerate | nondegenerate | The next theorem says that at the same width these flips are the only  |
| 25 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[Absorption with $\dm$ more units]{theorem}{thmAbsor |
| 26 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | In (i), the equation $\Wread[{:},S]\,\Wwrite[S,{:}] = -M$ is polynomia |
| 27 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | The proof matches the units of the two blocks. The even part of the ac |
| 28 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | para |  |  | \para{Networks of one block.} A residual network of one block is a blo |
| 29 | ReLU and GELU blocks: a skip is worth \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[Networks of one block]{proposition}{propOneBlockNet |
| 30 | ReLU\texorpdfstring{$^2$ | para |  |  | \subsection{ReLU\texorpdfstring{$^2$}{2}, gated and \texorpdfstring{$\ |
| 31 | ReLU\texorpdfstring{$^2$ | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 32 | ReLU\texorpdfstring{$^2$ | para |  |  | A block absorbs $xM$ if a block of the same kind satisfies \eqref{eq:a |
| 33 | ReLU\texorpdfstring{$^2$ | statement |  |  | \begin{restatable}[No width suffices]{theorem}{thmAbsorbHom}\label{thm |
| 34 | ReLU\texorpdfstring{$^2$ | para |  |  | The three cases of \cref{fig:reasons} are three one-line proofs. A hom |
| 35 | Attention blocks: no number of heads suffices | para |  |  | \subsection{Attention blocks: no number of heads suffices}\label{sec:a |
| 36 | Attention blocks: no number of heads suffices | para | Gamma, attention scores, attention block, score matrix, value-output product | Gamma, attention scores, score matrix, value-output product | An \emph{attention block} has $H$ heads of dimension $d_h$. Head $i$ h |
| 37 | Attention blocks: no number of heads suffices | para |  |  | Two inputs show that an attention block absorbs no linear term. Suppos |
| 38 | Attention blocks: no number of heads suffices | statement |  |  | \begin{restatable}[No absorption in attention blocks]{theorem}{thmAtte |
| 39 | Attention blocks: no number of heads suffices | para |  |  | The two inputs give one $h$ at which the two sides differ, and both si |
| 40 | Networks | para |  |  | \section{Networks}\label{sec:networks} \takeaway{The negative answers  |
| 41 | Networks | para |  |  | Recall that a network embeds its input as $h_0 = XE$ and reads out $y  |
| 42 | ReLU\texorpdfstring{$^2$ | para |  |  | \subsection{ReLU\texorpdfstring{$^2$}{2}, gated and \texorpdfstring{$\ |
| 43 | ReLU\texorpdfstring{$^2$ | statement |  |  | \begin{restatable}[No equality for ReLU$^2$, gated and $\tanh$ network |
| 44 | ReLU\texorpdfstring{$^2$ | para |  |  | The reasons are those of \cref{fig:reasons}, now for the whole network |
| 45 | Attention networks: never equal on long sequences | para |  |  | \subsection{Attention networks: never equal on long sequences}\label{s |
| 46 | Attention networks: never equal on long sequences | para |  |  | The comparison at $X = 0$ also settles networks of attention blocks. N |
| 47 | Attention networks: never equal on long sequences | statement |  |  | \begin{restatable}[Attention networks on long and short sequences]{the |
| 48 | Attention networks: never equal on long sequences | para |  |  | In the cases of (i), no number of heads helps. Neither does depth, onc |
| 49 | Networks under RMSNorm: almost never equal | para |  |  | \subsection{Networks under RMSNorm: almost never equal}\label{sec:rmsn |
| 50 | Networks under RMSNorm: almost never equal | para |  |  | Under RMSNorm the answer no longer depends on the kind of block. A ski |
| 51 | Networks under RMSNorm: almost never equal | statement |  |  | \begin{restatable}[Almost no equality under RMSNorm]{theorem}{thmRMSNe |
| 52 | Networks under RMSNorm: almost never equal | para |  |  | The proof compares rates of convergence along rays $tX$, as $t \to \in |
| 53 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | \subsection{ReLU and GELU networks without normalization: \texorpdfstr |
| 54 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | Without normalization, ReLU and GELU networks are the one case in whic |
| 55 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[$\dm$ more units per block suffice]{proposition}{pr |
| 56 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | Some of these units are needed, at least in the first block. |
| 57 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[The first block needs $2\dm$ units]{theorem}{thmAbs |
| 58 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | For ReLU the proof compares ranks. Near almost every input, a generic  |
| 59 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | For the first block, the two bounds meet when the residual first block |
| 60 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | \para{Injective residual blocks: every skipless block needs $2\dm$ uni |
| 61 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[Injective blocks: $2\dm$ units in every block]{prop |
| 62 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | The condition holds when every block has $\norm{\Wread}\,\norm{\Wwrite |
| 63 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | The proof turns on injectivity. If every residual block is injective,  |
| 64 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | For ReLU networks the condition cannot be dropped. On another open set |
| 65 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para | full | full | \para{Wide residual blocks: a bound from counting dimensions.} When th |
| 66 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | statement |  |  | \begin{restatable}[A lower bound from counting dimensions]{proposition |
| 67 | ReLU and GELU networks without normalization: \texorpdfstring{$\dm$ | para |  |  | A skipless network has a change of basis at each of its $L + 1$ hidden |
| 68 | Skipless networks are limits of residual ones | para |  |  | \section{Skipless networks are limits of residual ones}\label{sec:limi |
| 69 | Skipless networks are limits of residual ones | statement | F, the function of a network | F, the function of a network | \begin{restatable}[Skipless networks as limits of residual networks]{p |
| 70 | Skipless networks are limits of residual ones | para |  |  | \para{Idea of the proof.} The proof scales the reads of block $\ell$ b |
| 71 | Skipless networks are limits of residual ones | para |  |  | \para{Under RMSNorm.} With $\varepsilon = 0$, RMSNorm ignores the size |
| 72 | Related work | para |  |  | \section{Related work}\label{sec:related} |
| 73 | Related work | para |  |  | \para{Expressivity of residual networks.} \citet{lin2018resnet} show t |
| 74 | Related work | para |  |  | \para{Identifiability.} For $\tanh$ networks, the function determines  |
| 75 | Related work | para |  |  | \para{Training without skips.} Skipless networks train with weights pa |
| 76 | Conclusion | para |  |  | \section{Conclusion}\label{sec:conclusion} |
| 77 | Conclusion | para |  |  | Without normalization or biases, a trained residual ReLU or GELU netwo |
| 78 | Conclusion | para |  |  | \para{Open questions.} The unknown cells and the conditions of \cref{t |
| 79 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 80 | Use of AI | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

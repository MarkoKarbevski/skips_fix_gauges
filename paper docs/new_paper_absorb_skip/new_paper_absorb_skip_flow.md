# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | ReLU squared, absorb, d_model, the dimension, gated block, pre-RMSNorm | RMSNorm, ReLU squared, absorb, attention block, d_model, the dimension, gated block, generic / almost every, pre-RMSNorm, residual, skipless | \begin{abstract} Skip connections aid training and change which functi |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para |  |  | Skip connections are widely used in deep networks, from ResNets to tra |
| 3 | Introduction | para | B, the map of a block | B, the map of a block | Take a block $B$ without biases that acts on tokens of dimension $\dm$ |
| 4 | Introduction | para |  |  | ReLU and GELU allow exact absorption because $\sigma(z)-\sigma(-z)=z$. |
| 5 | Introduction | para | E and D, X, the input of a network, equal, readout / unembedding | E and D, X, the input of a network, equal, readout / unembedding | Two networks are \emph{equal} if they compute the same function. A res |
| 6 | Introduction | para | RMSNorm, epsilon of RMSNorm | epsilon of RMSNorm | In a pre-RMSNorm network, each learned branch and the readout receive  |
| 7 | Introduction | float | with pre-rmsnorm: | with pre-rmsnorm: | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.12} \ |
| 8 | Architectures and exact equivalence | para |  |  | \section{Architectures and exact equivalence}\label{sec:setup} |
| 9 | Architectures and exact equivalence | para | B_theta, Wread, Wwrite, theta, T, number of tokens, m, number of units, read / write (nouns) | B_theta, Wread, Wwrite, theta, T, number of tokens, m, number of units, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 10 | Architectures and exact equivalence | para | M, the linear term | M, the linear term | \para{Exact absorption.} We study the more general linear term $xM$, f |
| 11 | Architectures and exact equivalence | para | L, the number of blocks, residual, skipless | L, the number of blocks | \para{Networks.} A linear embedding $E \in \R^{d_{\mathrm{in}}\times\d |
| 12 | Architectures and exact equivalence | para | N(h) | N(h) | \para{Normalization.} RMSNorm, written $N$, divides each row $v$ of a  |
| 13 | Architectures and exact equivalence | para |  |  | \para{Biases.} With biases, ReLU, GELU, ReLU$^2$, and gated blocks can |
| 14 | Architectures and exact equivalence | para |  |  | \para{Scope.} Every MLP has at least $\dm$ hidden units, so its read c |
| 15 | Architectures and exact equivalence | para | generic / almost every |  | \para{Generic weights.} A statement holds for \emph{generic} weights,  |
| 16 | Exact absorption in a single block | para |  |  | \section{Exact absorption in a single block}\label{sec:oneblock} |
| 17 | ReLU and GELU: the cost of a linear skip | para |  |  | \subsection{ReLU and GELU: the cost of a linear skip}\label{sec:reluge |
| 18 | ReLU and GELU: the cost of a linear skip | para | mirror image, w_i and hat w_i, read and write of a unit | mirror image, w_i and hat w_i, read and write of a unit | ReLU and GELU both satisfy \begin{equation}\label{eq:odd} \sigma(z) -  |
| 19 | ReLU and GELU: the cost of a linear skip | para | widening the block. | widening the block. | \emph{Widening the block.} Choose a row $\gamma \in \R^{1\times\dm}$.  |
| 20 | ReLU and GELU: the cost of a linear skip | para | S, a set of units, at the same width. | S, a set of units, at the same width. | \emph{At the same width.} Flipping the read of unit $i$ to $-w_i$ chan |
| 21 | ReLU and GELU: the cost of a linear skip | para | nondegenerate | nondegenerate | Call a block \emph{nondegenerate} when the columns of $\Wread$ are non |
| 22 | ReLU and GELU: the cost of a linear skip | statement |  |  | \begin{restatable}[Absorption with $\dm$ more units]{theorem}{thmAbsor |
| 23 | ReLU and GELU: the cost of a linear skip | para |  |  | For each subset $S$, the condition in (i) is a polynomial equation in  |
| 24 | ReLU and GELU: the cost of a linear skip | para |  |  | The even part of the output determines which original read directions  |
| 25 | ReLU and GELU: the cost of a linear skip | para |  |  | The odd part then determines what remains of $M$ after sign flips of t |
| 26 | ReLU and GELU: the cost of a linear skip | para |  |  | \para{Networks of one block.} A residual network of one block is a blo |
| 27 | ReLU and GELU: the cost of a linear skip | statement |  |  | \begin{restatable}[Networks of one block]{proposition}{propOneBlockNet |
| 28 | MLP obstructions from scaling and boundedness | para |  |  | \subsection{MLP obstructions from scaling and boundedness}\label{sec:n |
| 29 | MLP obstructions from scaling and boundedness | para | t and u, a ray | t and u, a ray | For the remaining MLPs, compare the two sides of \eqref{eq:absorbask}  |
| 30 | MLP obstructions from scaling and boundedness | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 31 | MLP obstructions from scaling and boundedness | statement |  |  | \begin{restatable}[No width suffices]{theorem}{thmAbsorbHom}\label{thm |
| 32 | MLP obstructions from scaling and boundedness | para |  |  | The three obstructions in \cref{fig:reasons} follow from different pro |
| 33 | Attention: an obstruction from uniform averaging | para |  |  | \subsection{Attention: an obstruction from uniform averaging}\label{se |
| 34 | Attention: an obstruction from uniform averaging | para | Gamma, attention scores, H and d_h, attention block, score matrix, value-output product | Gamma, attention scores, H and d_h, score matrix, value-output product | An \emph{attention block} has $H$ heads of dimension $d_h$. Head $i$ h |
| 35 | Attention: an obstruction from uniform averaging | para |  |  | Suppose a skipless block matches the residual block on every input. Fi |
| 36 | Attention: an obstruction from uniform averaging | para |  |  | Now set one token to zero, choosing the last token when the mask is ca |
| 37 | Attention: an obstruction from uniform averaging | statement |  |  | \begin{restatable}[No absorption in attention blocks]{theorem}{thmAtte |
| 38 | Attention: an obstruction from uniform averaging | para |  |  | For a fixed candidate block, the output difference is analytic in $h$. |
| 39 | Exact skip removal in networks | para |  |  | \section{Exact skip removal in networks}\label{sec:networks} |
| 40 | Exact skip removal in networks | para |  |  | Replacing each block by an equivalent one is enough to preserve an unn |
| 41 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | \subsection{Width bounds for unnormalized ReLU and GELU networks}\labe |
| 42 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | The construction in \cref{sec:relugelu} replaces each residual block b |
| 43 | Width bounds for unnormalized ReLU and GELU networks | statement |  |  | \begin{restatable}[$\dm$ more units per block suffice]{proposition}{pr |
| 44 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | The construction gives an upper bound for each block. The first block  |
| 45 | Width bounds for unnormalized ReLU and GELU networks | statement |  |  | \begin{restatable}[The first block needs $2\dm$ units]{theorem}{thmAbs |
| 46 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | At generic weights, the residual ReLU network is locally linear with r |
| 47 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | For GELU, rescale the input by $t$ and divide the output by $t$. The b |
| 48 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | The bounds coincide for the first block when the residual first block  |
| 49 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | \para{Injective residual blocks: every skipless block needs $2\dm$ uni |
| 50 | Width bounds for unnormalized ReLU and GELU networks | statement |  |  | \begin{restatable}[Injective blocks: $2\dm$ units in every block]{prop |
| 51 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | The condition holds when every block has $\norm{\Wread}\,\norm{\Wwrite |
| 52 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | With embedding and readout of rank $\dm$, an injective residual stack  |
| 53 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | For ReLU, a different open set of weights illustrates why injectivity  |
| 54 | Width bounds for unnormalized ReLU and GELU networks | para | full | full | \para{Wide residual blocks.} A dimension count can force additional Re |
| 55 | Width bounds for unnormalized ReLU and GELU networks | statement |  |  | \begin{restatable}[A lower bound from counting dimensions]{proposition |
| 56 | Width bounds for unnormalized ReLU and GELU networks | para |  |  | A skipless network has a change of basis at each of its $L + 1$ hidden |
| 57 | Network obstructions from derivatives and growth | para |  |  | \subsection{Network obstructions from derivatives and growth}\label{se |
| 58 | Network obstructions from derivatives and growth | statement |  |  | \begin{restatable}[No equality for ReLU$^2$, gated and $\tanh$ network |
| 59 | Network obstructions from derivatives and growth | para |  |  | The direct skip path distinguishes the network derivatives at the orig |
| 60 | Attention stacks: the effect of sequence length | para |  |  | \subsection{Attention stacks: the effect of sequence length}\label{sec |
| 61 | Attention stacks: the effect of sequence length | para |  |  | At zero input, every head assigns uniform weight to its visible tokens |
| 62 | Attention stacks: the effect of sequence length | statement |  |  | \begin{restatable}[Attention networks on long and short sequences]{the |
| 63 | Attention stacks: the effect of sequence length | para |  |  | With a causal mask, row $j$ of $U$ averages the first $j$ tokens, so i |
| 64 | Pre-RMSNorm: the effect of input scale | para |  |  | \subsection{Pre-RMSNorm: the effect of input scale}\label{sec:rmsnets} |
| 65 | Pre-RMSNorm: the effect of input scale | para |  |  | Pre-RMSNorm creates an obstruction even when the block types differ. A |
| 66 | Pre-RMSNorm: the effect of input scale | statement |  |  | \begin{restatable}[Almost no equality under RMSNorm]{theorem}{thmRMSNe |
| 67 | Pre-RMSNorm: the effect of input scale | para |  |  | Along a ray $tX$, the skipless stack receives $N(tXE')$, with $E'$ its |
| 68 | Pre-RMSNorm: the effect of input scale | para |  |  | The residual stack carries $tXE$ and adds bounded block outputs to it. |
| 69 | Approximating skipless networks with residual networks | para |  |  | \section{Approximating skipless networks with residual networks}\label |
| 70 | Approximating skipless networks with residual networks | para |  |  | The previous section starts with a residual function and asks for an e |
| 71 | Approximating skipless networks with residual networks | statement | F, the function of a network | F, the function of a network | \begin{restatable}[Skipless networks as limits of residual networks]{p |
| 72 | Approximating skipless networks with residual networks | para |  |  | \para{Rescaling construction.} Aim for the residual state after block  |
| 73 | Approximating skipless networks with residual networks | para |  |  | \para{Effect of the regularizer.} At $\varepsilon=0$, RMSNorm removes  |
| 74 | Related work | para |  |  | \section{Related work}\label{sec:related} |
| 75 | Related work | para |  |  | \para{Approximation and exact representation.} \citet{lin2018resnet} p |
| 76 | Related work | para |  |  | \para{Identifiability.} Recovering units from the function is central  |
| 77 | Related work | para |  |  | \para{Training skipless models.} Prior work trains skipless architectu |
| 78 | Conclusions and open problems | para |  |  | \section{Conclusions and open problems}\label{sec:conclusion} |
| 79 | Conclusions and open problems | para |  |  | For bias-free ReLU and GELU networks without normalization, the single |
| 80 | Conclusions and open problems | para |  |  | \para{Open questions.} \begin{enumerate}[label=(\arabic*)] \item Netwo |
| 81 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 82 | Use of AI | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

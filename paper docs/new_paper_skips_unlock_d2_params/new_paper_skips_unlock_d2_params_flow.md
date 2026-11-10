# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | d_model, the width, functional dimension, identity skip, pre-RMSNorm | RMSNorm, change of basis, d_model, the width, functional dimension, identity skip, pre-RMSNorm, residual | \begin{abstract} Residual and skipless networks with the same blocks h |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para |  |  | Skip connections are standard in modern deep networks \citep{he2016res |
| 3 | Introduction | para |  |  | In a skipless network, changing the coordinates of a hidden state can  |
| 4 | Introduction | para | G, a change of basis, L, the number of blocks, W, a generic weight matrix, h, a hidden state | G, a change of basis, L, the number of blocks, h, a hidden state | To see the constraint, consider an unnormalized network. Let $G$ be an |
| 5 | Introduction | para | A_l, a learned skip, RMSNorm, epsilon of RMSNorm, learned skip, readout / unembedding | A_l, a learned skip, epsilon of RMSNorm, learned skip, readout / unembedding, redundancy | These basis choices account for a concrete redundancy. An arbitrary in |
| 6 | Introduction | para |  | generic | The disappearance of a symmetry gives a difference between two upper b |
| 7 | Introduction | para | P, the number of parameters, running example | P, the number of parameters, running example | Our running example uses three blocks of eight GELU units, $\dm=4$, an |
| 8 | Introduction | float |  |  | \begin{figure}[t] \centering \includegraphics[width=0.94\linewidth]{fi |
| 9 | Introduction | float | analytic blocks, functional dimension added by the skips | functional dimension added by the skips | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 10 | Network architectures and assumptions | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | \section{Network architectures and assumptions}\label{sec:setup} \para |
| 11 | Network architectures and assumptions | para | E and D, residual | E and D | \para{Networks.} A linear embedding $E\in\R^{d_{\mathrm{in}}\times\dm} |
| 12 | Network architectures and assumptions | para | N(h) | N(h) | \para{Normalization.} RMSNorm, written $N$, divides each row $v$ of $h |
| 13 | Network architectures and assumptions | para | generic |  | \para{Scope.} Networks have no biases, and their inputs are continuous |
| 14 | Independent bases in skipless networks | para |  |  | \section{Hidden-state symmetries and exact parameter reductions}\label |
| 15 | Independent bases in skipless networks | para | change of basis | W, a generic weight matrix | Between consecutive skipless blocks, the state is the output of one li |
| 16 | Independent bases in skipless networks | statement | W_1, the chosen block | W_1, the chosen block | \begin{restatable}[Exact reduction without skips]{proposition}{propSki |
| 17 | Independent bases in skipless networks | para |  |  | The same normalization can use rows of a write: choose an invertible s |
| 18 | Independent bases in skipless networks | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 19 | Eliminating invertible learned skips | para |  |  | \subsection{Eliminating invertible learned skips}\label{sec:learned} |
| 20 | Eliminating invertible learned skips | para | Lambda, identity units | Lambda, identity units | A learned skip acts as $\dm$ \emph{identity units}, hidden units whose |
| 21 | Eliminating invertible learned skips | statement |  |  | \begin{restatable}[Learned skips reduce to identity skips]{theorem}{th |
| 22 | Eliminating invertible learned skips | para |  |  | Invertibility makes all $L\dm^2$ learned-skip entries removable withou |
| 23 | A common basis under identity skips | para |  |  | \subsection{A common basis under identity skips}\label{sec:global}\lab |
| 24 | A common basis under identity skips | para |  |  | When every skip is fixed to the identity, the two basis choices at a b |
| 25 | A common basis under identity skips | statement |  |  | \begin{restatable}[One change of basis for the whole network]{theorem} |
| 26 | A common basis under identity skips | para |  |  | The dimension drops by $L\dm^2$. This counts only the hidden-state cha |
| 27 | Orthogonal symmetries under normalization | para |  |  | \subsection{Orthogonal symmetries under normalization}\label{sec:norm} |
| 28 | Orthogonal symmetries under normalization | para |  |  | With pre-RMSNorm, the reads and the skips act on different versions of |
| 29 | Orthogonal symmetries under normalization | statement |  |  | \begin{restatable}[Orthogonal changes of basis under RMSNorm]{theorem} |
| 30 | Orthogonal symmetries under normalization | para |  |  | \para{The triangular part of a learned skip.} The orthogonal transform |
| 31 | Orthogonal symmetries under normalization | para |  |  | \para{LayerNorm.} LayerNorm is RMSNorm after a projection that removes |
| 32 | Counts for ViT-B and Llama-3.1 | para |  |  | \subsection{Counts for ViT-B and Llama-3.1}\label{sec:trained} |
| 33 | Counts for ViT-B and Llama-3.1 | para |  |  | The skipless ViT-B of \citet{ji2026cutting} has $\dm=768$ and $25$ hid |
| 34 | From symmetry counts to functional dimension | para |  |  | \section{From symmetry counts to functional dimension}\label{sec:gain} |
| 35 | Functional dimension and redundancy | para |  |  | \subsection{Functional dimension and redundancy}\label{sec:fd} |
| 36 | Functional dimension and redundancy | statement | F_theta, redundancy | F_theta | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 37 | Functional dimension and redundancy | para |  |  | An infinitesimal parameter change along a symmetry orbit lies in the k |
| 38 | Functional dimension and redundancy | para |  |  | \begin{example}[A product of three matrices]\label{ex:three} The linea |
| 39 | Dimension bounds from symmetry orbits | para |  |  | \subsection{Dimension bounds from symmetry orbits}\label{sec:count} |
| 40 | Dimension bounds from symmetry orbits | para | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | script G, symmetries inside blocks, symmetries inside the blocks | The changes of basis of one hidden state form a group $\G$: $\GL(\dm)$ |
| 41 | Dimension bounds from symmetry orbits | statement |  | s, symmetries inside | \begin{restatable}[Upper bounds]{theorem}{thmUnlock}\label{thm:unlock} |
| 42 | Dimension bounds from symmetry orbits | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 43 | Dimension bounds from symmetry orbits | para |  |  | If both architectures attain their bounds, each skip adds $\dim\G$ to  |
| 44 | Dimension bounds from symmetry orbits | para |  |  | \para{Learned skips.} A network with learned skips has $L\dm^2$ more p |
| 45 | Dimension bounds from symmetry orbits | para |  |  | \para{The gain in a transformer.} Under the equality condition, a resi |
| 46 | Sharp bounds at one block and at depth | para |  |  | \subsection{Sharp bounds at one block and at depth}\label{sec:onelayer |
| 47 | Sharp bounds at one block and at depth | para |  |  | The one-block result gives an exact comparison without normalization a |
| 48 | Sharp bounds at one block and at depth | statement |  |  | \begin{restatable}[Equality for one block]{theorem}{thmOneBlock}\label |
| 49 | Sharp bounds at one block and at depth | statement |  |  | \begin{restatable}[Equality for residual networks at any depth]{theore |
| 50 | Sharp bounds at one block and at depth | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 51 | Sharp bounds at one block and at depth | para |  |  | \para{Why the bounds are attained.} With one block, the relevant matri |
| 52 | Sharp bounds at one block and at depth | para |  | analytic blocks | At depth, scale the writes by a small $\tau$. To first order, the resi |
| 53 | Sharp bounds at one block and at depth | para |  |  | For skipless $\tanh$ networks, identifiability recovers the products b |
| 54 | Consequences for exact skip removal | para |  |  | \subsection{Consequences for exact skip removal}\label{sec:classes} |
| 55 | Consequences for exact skip removal | para |  |  | A larger functional dimension has a consequence for exact representati |
| 56 | Consequences for exact skip removal | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 57 | Consequences for exact skip removal | para |  |  | In the GELU case, each extra skipless unit contributes $2\dm$ paramete |
| 58 | Measured ranks and the skipless conjecture | para |  |  | \subsection{Measured ranks and the skipless conjecture}\label{sec:meas |
| 59 | Measured ranks and the skipless conjecture | para |  |  | A Jacobian on a finite input batch gives a lower bound on functional d |
| 60 | Measured ranks and the skipless conjecture | float |  |  | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 61 | Measured ranks and the skipless conjecture | para |  |  | Ranks below the symmetry bound have two different explanations in thes |
| 62 | Measured ranks and the skipless conjecture | statement |  |  | \begin{conjecture}[Equality without skips]\label{conj:equality} With o |
| 63 | Measured ranks and the skipless conjecture | para |  |  | Without normalization, \cref{thm:oneblock} proves the conjecture for o |
| 64 | Measured ranks and the skipless conjecture | para |  |  | \para{One-hot tokens.} With one-hot tokens under RMSNorm, the rows of  |
| 65 | Related work | para |  |  | \section{Related work}\label{sec:related} |
| 66 | Related work | para |  |  | \para{Changes of basis across blocks.} \citet{zhao2023symmetries} desc |
| 67 | Related work | para |  |  | \para{Residual-stream invariance and parameter reduction.} The residua |
| 68 | Related work | para |  |  | \para{Identifiability and Jacobian rank.} \citet{wang2025gauge} charac |
| 69 | Related work | para |  |  | \para{Functional dimension.} \citet{grigsby2022functional} define func |
| 70 | Related work | para |  |  | \para{Training with and without skips.} Skip connections ease optimiza |
| 71 | Related work | para |  |  | \para{Exact removal of identity skips.} Our companion paper constructs |
| 72 | Conclusions and open problems | para |  |  | \section{Conclusions and open problems}\label{sec:outlook}\label{sec:c |
| 73 | Conclusions and open problems | para |  |  | A fixed skip constrains the relative bases at its endpoints. Across de |
| 74 | Conclusions and open problems | para |  |  | The main open problem is to characterize redundancy in deep skipless n |
| 75 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 76 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 77 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

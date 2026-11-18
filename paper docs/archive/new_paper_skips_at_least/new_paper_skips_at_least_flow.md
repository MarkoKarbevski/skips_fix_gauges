# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para |  | RMSNorm, d_model, the width, functional dimension, pre-RMSNorm, redundancy, residual | \begin{abstract} It was recently shown that skip connections change th |
| 1 | abstract | float | L, the number of blocks, d_hidden, the number of hidden units | L, the number of blocks, d_hidden, the number of hidden units | \begin{figure}[!h] \centering \includegraphics[width=0.94\linewidth]{f |
| 2 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 3 | Introduction | para | d_model, the width | per block | Skip connections are a building block of almost every deep network tra |
| 4 | Introduction | para |  |  | Skipless networks have recently been trained to varying degrees of suc |
| 5 | Introduction | para |  | change of basis, readout / unembedding | \para{One change of basis per hidden state.} Without skips, the basis  |
| 6 | Introduction | para | functional dimension | generic | \para{Functional dimension.} By the degrees of freedom of a network we |
| 7 | Contributions | para |  |  | \subsection{Contributions}\label{sec:contributions} |
| 8 | Contributions | para | P, the number of parameters, analytic blocks, s, symmetries inside | P, the number of parameters, analytic blocks, s, symmetries inside | \para{Main result.} Residual networks attain the upper bound from the  |
| 9 | Contributions | para |  |  | \para{Attention-only transformers.} For attention-only transformers wi |
| 10 | Contributions | para |  |  | \para{Where the gain is exact.} The skips raise the functional dimensi |
| 11 | Contributions | para | identity skip, learned skip, locally identifiable | identity skip, learned skip, locally identifiable | \para{Further results.} A \emph{learned skip} multiplies the hidden st |
| 12 | Contributions | float | ReLU squared, functional dimension added by the skips | ReLU squared, functional dimension added by the skips | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1}\se |
| 13 | Related work | para |  |  | \subsection{Related work}\label{sec:related} |
| 14 | Related work | para |  |  | We name the works closest to ours, and \cref{app:related} discusses th |
| 15 | Setup | para |  |  | \section{Setup}\label{sec:setup} This section fixes the networks that  |
| 16 | Setup | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, T, number of tokens, gated block, h, a hidden state, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, T, number of tokens, gated block, h, a hidden state, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 17 | Setup | para | A_l, a learned skip, E and D, F_theta, generic, per block, readout / unembedding, residual | A_l, a learned skip, E and D, F_theta | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 18 | Setup | para | epsilon of RMSNorm, pre-RMSNorm, under rmsnorm | epsilon of RMSNorm, under rmsnorm | \para{Normalization.} RMSNorm with the constant $\varepsilon > 0$ is t |
| 19 | Setup | para |  |  | \para{Scope.} Networks have no biases, and their inputs range over all |
| 20 | Changes of basis that preserve the function | para |  |  | \section{Changes of basis that preserve the function}\label{sec:reduce |
| 21 | Changes of basis that preserve the function | para | G, a change of basis | G, a change of basis | The results of this section rest on one symmetry, which the first two  |
| 22 | Changes of basis that preserve the function | statement | W, a generic weight matrix, change of basis | W, a generic weight matrix | \begin{definition}[Change of basis]\label{def:cob} In a skipless and i |
| 23 | Changes of basis that preserve the function | para |  |  | \para{What is known.} This section builds on results that are known, i |
| 24 | Changes of basis that preserve the function | para | script G | script G | \para{Pre-RMSNorm.} Under pre-RMSNorm a block reads $N_\varepsilon(h)$ |
| 25 | Changes of basis that preserve the function | para |  |  | \para{What this section builds.} We use the symmetry to remove paramet |
| 26 | Skipless networks: one change of basis per hidden state | para |  |  | \subsection{Skipless networks: one change of basis per hidden state}\l |
| 27 | Skipless networks: one change of basis per hidden state | para | W_1, the chosen block | W_1, the chosen block | In a skipless network, a change of basis in $\G$ at any hidden state p |
| 28 | Skipless networks: one change of basis per hidden state | statement |  |  | \begin{restatable}[Exact reduction without skips]{proposition}{propSki |
| 29 | Skipless networks: one change of basis per hidden state | para |  |  | Any $\dm$ columns that form an invertible matrix serve as $W_1$, and r |
| 30 | Skipless networks: one change of basis per hidden state | para |  |  | In an attention block with $Hd_h = \dm$, the matrices $W_Q$ and $W_O$  |
| 31 | Telescoping (generic) learned skips to identity skips | para |  |  | \subsection{Telescoping (generic) learned skips to identity skips}\lab |
| 32 | Telescoping (generic) learned skips to identity skips | para |  |  | In \cref{sec:skipless} the change of basis at each hidden state was ch |
| 33 | Telescoping (generic) learned skips to identity skips | para |  |  | The skip $A_\ell$ multiplies $h_{\ell-1}$, and the result is added to  |
| 34 | Telescoping (generic) learned skips to identity skips | para | Lambda | Lambda | Let every $A_\ell$ be invertible, as it is at generic parameters. The  |
| 35 | Telescoping (generic) learned skips to identity skips | statement |  |  | \begin{restatable}[Learned skips reduce to identity skips]{theorem}{th |
| 36 | Telescoping (generic) learned skips to identity skips | para |  |  | So the networks with invertible learned skips have $L\dm^2$ more param |
| 37 | Identity skips: one change of basis for the whole network | para |  |  | \subsection{Identity skips: one change of basis for the whole network} |
| 38 | Identity skips: one change of basis for the whole network | para |  |  | \Cref{sec:learned} turned invertible learned skips into identity skips |
| 39 | Identity skips: one change of basis for the whole network | para |  |  | With a change of basis $G_{\ell-1}$ at $h_{\ell-1}$ and $G_\ell$ at $h |
| 40 | Identity skips: one change of basis for the whole network | statement |  |  | \begin{restatable}[One change of basis for the whole network]{theorem} |
| 41 | Identity skips: one change of basis for the whole network | para |  |  | So the $L$ skips remove $L\dim\G$ dimensions from this group, and \cre |
| 42 | LayerNorm and trained models | para |  |  | \subsection{LayerNorm and trained models}\label{sec:norm} |
| 43 | LayerNorm and trained models | para |  |  | The counts of this section carry over to LayerNorm, and the reductions |
| 44 | LayerNorm and trained models | para |  |  | \para{LayerNorm.} LayerNorm is RMSNorm after a projection that removes |
| 45 | LayerNorm and trained models | para |  |  | \para{Trained models.}\label{sec:trained} In the skipless ViT-B \citep |
| 46 | Functional dimension with and without skips | para |  |  | \section{Functional dimension with and without skips}\label{sec:gain}  |
| 47 | Functional dimension and its upper bound | para |  |  | \subsection{Functional dimension and its upper bound}\label{sec:fd}\la |
| 48 | Functional dimension and its upper bound | para |  |  | We define the functional dimension and the redundancy, and compute bot |
| 49 | Functional dimension and its upper bound | statement | redundancy |  | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 50 | Functional dimension and its upper bound | para |  |  | A continuous symmetry adds to the redundancy: if a continuous family o |
| 51 | Functional dimension and its upper bound | para |  |  | \begin{example}[Not all reductions are maximal]\label{ex:three} The li |
| 52 | Functional dimension and its upper bound | para | symmetries inside blocks, symmetries inside the blocks | symmetries inside blocks, symmetries inside the blocks | Two kinds of symmetry bound the functional dimension. The first are th |
| 53 | Functional dimension and its upper bound | statement |  |  | \begin{restatable}[Upper bounds]{theorem}{thmUnlock}\label{thm:unlock} |
| 54 | Functional dimension and its upper bound | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 55 | Functional dimension and its upper bound | para |  |  | When the residual network satisfies it, each skip unlocks $\dim\G$ par |
| 56 | Functional dimension and its upper bound | statement | identifiable up to its symmetries | identifiable up to its symmetries | \begin{definition}[Identifiability up to symmetries]\label{def:ident}  |
| 57 | Functional dimension and its upper bound | para |  |  | The notion follows \citet{vlacic2020affine}, \citet{stock2021embedding |
| 58 | Functional dimension and its upper bound | statement |  |  | \begin{restatable}[The equality condition and local identifiability]{p |
| 59 | Functional dimension and its upper bound | para |  |  | The proposition compares only parameters that are close to each other: |
| 60 | Functional dimension and its upper bound | para |  |  | \para{The gain in a transformer.} Under the equality condition, a resi |
| 61 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 62 | When the bounds are attained | para |  |  | The equality condition is a hypothesis, and it can fail (\cref{sec:mea |
| 63 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for one block]{theorem}{thmOneBlock}\label |
| 64 | When the bounds are attained | para |  |  | For three kinds of block without a skip, the equality condition of \cp |
| 65 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for residual networks at any depth]{theore |
| 66 | When the bounds are attained | para |  |  | \begin{corollary}[Residual networks are locally identifiable]\label{co |
| 67 | When the bounds are attained | para |  |  | This is \cref{thm:resdepth} together with \cref{prop:localid}. Whether |
| 68 | When the bounds are attained | para |  |  | \begin{corollary}[Attention-only transformers: Conjecture~2.4 of \cite |
| 69 | When the bounds are attained | para |  |  | The corollary answers the conjecture of \citet{henry2026generic}, that |
| 70 | When the bounds are attained | para |  |  | \para{Proof sketches.} With one block, the parameters enter the functi |
| 71 | Residual and skipless networks compute different functions | para |  |  | \subsection{Residual and skipless networks compute different functions |
| 72 | Residual and skipless networks compute different functions | para | pointwise limit | pointwise limit | The gain in functional dimension says something about the functions th |
| 73 | Residual and skipless networks compute different functions | para |  |  | \citet{mijoski2026worth} show that, without normalization, every skipl |
| 74 | Residual and skipless networks compute different functions | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 75 | Residual and skipless networks compute different functions | para |  |  | The reason is the gap between the two bounds of \cref{thm:unlock}: on  |
| 76 | Numerical ranks at depth, and a conjecture | para |  |  | \subsection{Numerical ranks at depth, and a conjecture}\label{sec:meas |
| 77 | Numerical ranks at depth, and a conjecture | para |  |  | For skipless networks at depth, \cref{thm:unlock} gives an upper bound |
| 78 | Numerical ranks at depth, and a conjecture | para |  |  | The rank of the Jacobian on a large batch of inputs (\cref{app:checks} |
| 79 | Numerical ranks at depth, and a conjecture | para |  |  | In two cases the measured rank stays below the upper bound. In skiples |
| 80 | Numerical ranks at depth, and a conjecture | statement |  |  | \begin{conjecture}[Equality without skips]\label{conj:equality} With o |
| 81 | Numerical ranks at depth, and a conjecture | para |  |  | The analogue of the conjecture is known for polynomial activations. \c |
| 82 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 83 | Conclusion | para |  |  | Skip connections change how a network uses its parameters. Without ski |
| 84 | Conclusion | para |  |  | \para{Open questions.} For skipless networks at depth we do not prove  |
| 85 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 86 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 87 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

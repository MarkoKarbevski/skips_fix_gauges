# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para |  | RMSNorm, d_model, the width, functional dimension, per block, pre-RMSNorm | \begin{abstract} Skip connections change the function class of an MLP  |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro}\label{sec:related} |
| 2 | Introduction | para | d_model, the width |  | Skip connections are a building block of almost every deep network tra |
| 3 | Introduction | para |  | residual | Skipless networks are now trained as well. \citet{he2023shortcuts} tra |
| 4 | Introduction | para | L, the number of blocks | L, the number of blocks, change of basis, readout / unembedding | \para{Where the degrees of freedom come from.} Without skips, the basi |
| 5 | Introduction | para | functional dimension | generic | \para{Functional dimension.} By the degrees of freedom of a network we |
| 6 | Introduction | float |  |  | \begin{figure}[t] \centering \includegraphics[width=0.94\linewidth]{fi |
| 7 | Introduction | para |  | limit | \para{Functional dimension and equality of functions.} The result of \ |
| 8 | Introduction | para | A_l, a learned skip, identity skip, learned skip | A_l, a learned skip, identity skip, learned skip, redundancy | \para{Contributions and related work.} \Cref{tab:results} lists the re |
| 9 | Introduction | float | analytic blocks, functional dimension added by the skips | functional dimension added by the skips | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 10 | Setup | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, h, a hidden state, m, number of units, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, h, a hidden state, m, number of units, read / write (nouns) | \section{Setup}\label{sec:setup} \para{Blocks.} A hidden state is a ma |
| 11 | Setup | para | E and D, P, the number of parameters, per block, readout / unembedding, residual | E and D, P, the number of parameters | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 12 | Setup | para | N(h), RMSNorm, epsilon of RMSNorm, pre-RMSNorm, under rmsnorm | N(h), epsilon of RMSNorm, under rmsnorm | \para{Normalization.} RMSNorm, written $N$, divides each row $v$ of $h |
| 13 | Setup | para | generic |  | \para{Scope.} Networks have no biases, and their inputs are continuous |
| 14 | Changes of basis that preserve the function | para |  |  | \section{Changes of basis that preserve the function}\label{sec:reduce |
| 15 | Changes of basis that preserve the function | para | G, a change of basis | G, a change of basis | The results of this section rest on one symmetry, which the first two  |
| 16 | Changes of basis that preserve the function | statement | W, a generic weight matrix, change of basis | W, a generic weight matrix | \begin{definition}[Change of basis]\label{def:cob} In a skipless and i |
| 17 | Changes of basis that preserve the function | para |  |  | \citet{zhao2023symmetries} formalize this symmetry for MLPs. It adapts |
| 18 | Changes of basis that preserve the function | para |  |  | The computation \eqref{eq:product} uses only the form \eqref{eq:block} |
| 19 | Skipless networks: one change of basis per hidden state | para |  |  | \subsection{Skipless networks: one change of basis per hidden state}\l |
| 20 | Skipless networks: one change of basis per hidden state | para |  |  | In a skipless network without normalization, the invariance \eqref{eq: |
| 21 | Skipless networks: one change of basis per hidden state | statement | W_1, the chosen block | W_1, the chosen block | \begin{restatable}[Exact reduction without skips]{proposition}{propSki |
| 22 | Skipless networks: one change of basis per hidden state | para |  |  | Rows of a write work too: if $\dm$ rows of the write into $h_\ell$ for |
| 23 | Skipless networks: one change of basis per hidden state | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 24 | Learned skips: reduction to identity skips | para |  |  | \subsection{Learned skips: reduction to identity skips}\label{sec:lear |
| 25 | Learned skips: reduction to identity skips | para | Lambda, identity units | Lambda, identity units | In this subsection, networks have no normalization. Under RMSNorm a sk |
| 26 | Learned skips: reduction to identity skips | statement |  |  | \begin{restatable}[Learned skips reduce to identity skips]{theorem}{th |
| 27 | Learned skips: reduction to identity skips | para |  |  | So the networks with invertible learned skips have $L\dm^2$ more param |
| 28 | Identity skips: one change of basis for the whole network | para |  |  | \subsection{Identity skips: one change of basis for the whole network} |
| 29 | Identity skips: one change of basis for the whole network | para |  |  | A residual network keeps one change of basis, the same at all its hidd |
| 30 | Identity skips: one change of basis for the whole network | statement |  |  | \begin{restatable}[One change of basis for the whole network]{theorem} |
| 31 | Identity skips: one change of basis for the whole network | para |  |  | So the $L$ skips remove $L\dm^2$ dimensions from this group, and \cref |
| 32 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \subsection{RMSNorm and LayerNorm: orthogonal changes of basis}\label{ |
| 33 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | With pre-RMSNorm, the network with learned skips computes \begin{equat |
| 34 | RMSNorm and LayerNorm: orthogonal changes of basis | statement |  |  | \begin{restatable}[Orthogonal changes of basis under RMSNorm]{theorem} |
| 35 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Learned skips under RMSNorm.} In \eqref{eq:prenorm} the skip $A_ |
| 36 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{LayerNorm.} LayerNorm is RMSNorm after a projection that removes |
| 37 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Trained models.}\label{sec:trained} The reduction applies to tra |
| 38 | Functional dimension with and without skips | para |  |  | \section{Functional dimension with and without skips}\label{sec:gain}  |
| 39 | Definition and a linear example | para |  |  | \subsection{Definition and a linear example}\label{sec:fd} |
| 40 | Definition and a linear example | statement | F_theta, redundancy | F_theta | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 41 | Definition and a linear example | para |  |  | A continuous symmetry adds to the redundancy: if a continuous family o |
| 42 | Definition and a linear example | para |  |  | \begin{example}[A product of three matrices]\label{ex:three} The linea |
| 43 | Upper bounds from the symmetries | para |  |  | \subsection{Upper bounds from the symmetries}\label{sec:count} |
| 44 | Upper bounds from the symmetries | para | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | Two kinds of symmetry bound the functional dimension. The changes of b |
| 45 | Upper bounds from the symmetries | statement |  |  | \begin{restatable}[Upper bounds]{theorem}{thmUnlock}\label{thm:unlock} |
| 46 | Upper bounds from the symmetries | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 47 | Upper bounds from the symmetries | para |  |  | When the residual network satisfies it, each skip unlocks $\dim\G$ par |
| 48 | Upper bounds from the symmetries | statement | identifiable up to its symmetries, locally identifiable | identifiable up to its symmetries, locally identifiable | \begin{definition}[Identifiability up to symmetries]\label{def:ident}  |
| 49 | Upper bounds from the symmetries | para |  |  | \citet{vlacic2020affine} define identifiability up to an equivalence r |
| 50 | Upper bounds from the symmetries | para |  | analytic blocks | \para{Functional dimension and identifiability.} The two notions meet  |
| 51 | Upper bounds from the symmetries | para |  |  | \para{The gain in a transformer.} Under the equality condition, a resi |
| 52 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 53 | When the bounds are attained | para |  |  | The equality condition is a hypothesis, and it can fail (\cref{sec:mea |
| 54 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for one block]{theorem}{thmOneBlock}\label |
| 55 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for residual networks at any depth]{theore |
| 56 | When the bounds are attained | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 57 | When the bounds are attained | para |  |  | \para{Proof sketches.} With one block, the parameters enter the functi |
| 58 | Residual and skipless networks compute different functions | para |  |  | \subsection{Residual and skipless networks compute different functions |
| 59 | Residual and skipless networks compute different functions | para | limit |  | A network $F$ is a \emph{limit} of a family of networks if, for all in |
| 60 | Residual and skipless networks compute different functions | para | definable in an o-minimal structure | definable in an o-minimal structure | By \cref{def:fd,thm:resdepth}, the Jacobian of the residual network ha |
| 61 | Residual and skipless networks compute different functions | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 62 | Residual and skipless networks compute different functions | para |  |  | For GELU blocks without normalization, \citet{mijoski2026worth} show t |
| 63 | Numerical ranks at depth, and a conjecture | para |  |  | \subsection{Numerical ranks at depth, and a conjecture}\label{sec:meas |
| 64 | Numerical ranks at depth, and a conjecture | para |  |  | At depth we compute the rank of the Jacobian on a large batch of input |
| 65 | Numerical ranks at depth, and a conjecture | float |  |  | \begin{table}[b] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 66 | Numerical ranks at depth, and a conjecture | para |  |  | In two cases the measured rank stays below the upper bound. In skiples |
| 67 | Numerical ranks at depth, and a conjecture | statement |  |  | \begin{conjecture}[Equality without skips]\label{conj:equality} With o |
| 68 | Numerical ranks at depth, and a conjecture | para |  |  | For ReLU$^2$ and ReGLU blocks we expect the equality condition to hold |
| 69 | Numerical ranks at depth, and a conjecture | para |  |  | \para{One-hot tokens.} With one-hot tokens under RMSNorm, the rows of  |
| 70 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 71 | Conclusion | para |  |  | Skip connections change how a network uses its parameters. Without ski |
| 72 | Conclusion | para |  |  | \para{Open questions.} The equality condition at depth is open for the |
| 73 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 74 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 75 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

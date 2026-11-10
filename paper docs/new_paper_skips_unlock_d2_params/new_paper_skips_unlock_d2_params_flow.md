# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | d_model, the width, functional dimension | RMSNorm, change of basis, d_model, the width, functional dimension, per block, residual | \begin{abstract} Residual and skipless networks with the same blocks h |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro}\label{sec:related} |
| 2 | Introduction | para |  |  | Skip connections are a building block of almost every deep network tra |
| 3 | Introduction | para | epsilon of RMSNorm, pre-RMSNorm, readout / unembedding | epsilon of RMSNorm, pre-RMSNorm, readout / unembedding | Skipless networks are now trained as well. \citet{he2023shortcuts} tra |
| 4 | Introduction | para | G, a change of basis, W, a generic weight matrix, h, a hidden state | G, a change of basis, h, a hidden state | \para{Hidden states have free bases.} Without normalization, a skiples |
| 5 | Introduction | para | L, the number of blocks | L, the number of blocks | \para{A free basis removes $\dm^2$ parameters.} A suitable $G$ sets a  |
| 6 | Introduction | para | P, the number of parameters, running example | P, the number of parameters, redundancy, running example | \para{Functional dimension.} Our measure is the \emph{functional dimen |
| 7 | Introduction | float |  |  | \begin{figure}[t] \centering \includegraphics[width=0.94\linewidth]{fi |
| 8 | Introduction | para |  |  | \para{A gain in dimension and an equality of functions.} \citet{mijosk |
| 9 | Introduction | para | A_l, a learned skip, identity skip, identity units, learned skip | A_l, a learned skip, generic, identity skip, learned skip | \para{Contributions and related work.} Each item states what we add, a |
| 10 | Introduction | float | analytic blocks, functional dimension added by the skips | functional dimension added by the skips | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 11 | Setup | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | \section{Setup}\label{sec:setup} \para{Blocks.} A hidden state is a ma |
| 12 | Setup | para | E and D, per block, residual | E and D | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 13 | Setup | para | N(h), RMSNorm | N(h) | \para{Normalization.} RMSNorm, written $N$, divides each row $v$ of $h |
| 14 | Setup | para | generic |  | \para{Scope.} Networks have no biases, and their inputs are continuous |
| 15 | Skipless networks: one change of basis per hidden state | para |  |  | \section{Changes of basis that preserve the function}\label{sec:reduce |
| 16 | Skipless networks: one change of basis per hidden state | para | change of basis | W, a generic weight matrix | Without normalization, nothing nonlinear happens between the write of  |
| 17 | Skipless networks: one change of basis per hidden state | statement | W_1, the chosen block | W_1, the chosen block | \begin{restatable}[Exact reduction without skips]{proposition}{propSki |
| 18 | Skipless networks: one change of basis per hidden state | para |  |  | Rows of a write work too: if $\dm$ rows of the write into $h_\ell$ for |
| 19 | Skipless networks: one change of basis per hidden state | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 20 | Learned skips: reduction to identity skips | para |  |  | \subsection{Learned skips: reduction to identity skips}\label{sec:lear |
| 21 | Learned skips: reduction to identity skips | para | Lambda | Lambda, identity units | A learned skip, which adds $hA$ in place of $h$, is a block of $\dm$ \ |
| 22 | Learned skips: reduction to identity skips | statement |  |  | \begin{restatable}[Learned skips reduce to identity skips]{theorem}{th |
| 23 | Learned skips: reduction to identity skips | para |  |  | So all $L\dm^2$ parameters of invertible learned skips can be removed, |
| 24 | Identity skips: one change of basis for the whole network | para |  |  | \subsection{Identity skips: one change of basis for the whole network} |
| 25 | Identity skips: one change of basis for the whole network | para |  |  | A residual network keeps one change of basis, the same at all its hidd |
| 26 | Identity skips: one change of basis for the whole network | statement |  |  | \begin{restatable}[One change of basis for the whole network]{theorem} |
| 27 | Identity skips: one change of basis for the whole network | para |  |  | So the $L$ skips remove $L\dm^2$ dimensions from this group, and \cref |
| 28 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \subsection{RMSNorm and LayerNorm: orthogonal changes of basis}\label{ |
| 29 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | With pre-RMSNorm, the network with learned skips computes \begin{equat |
| 30 | RMSNorm and LayerNorm: orthogonal changes of basis | statement |  |  | \begin{restatable}[Orthogonal changes of basis under RMSNorm]{theorem} |
| 31 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Learned skips under RMSNorm.} Under RMSNorm, part of a learned s |
| 32 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{LayerNorm.} LayerNorm is RMSNorm after a projection that removes |
| 33 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Trained models.}\label{sec:trained} The reduction applies to tra |
| 34 | Functional dimension with and without skips | para |  |  | \section{Functional dimension with and without skips}\label{sec:gain}  |
| 35 | Definition and a linear example | para |  |  | \subsection{Definition and a linear example}\label{sec:fd} |
| 36 | Definition and a linear example | statement | F_theta, redundancy | F_theta | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 37 | Definition and a linear example | para |  |  | A continuous symmetry adds to the redundancy: if a continuous family o |
| 38 | Definition and a linear example | para |  |  | \begin{example}[A product of three matrices]\label{ex:three} The linea |
| 39 | Upper bounds from the symmetries | para |  |  | \subsection{Upper bounds from the symmetries}\label{sec:count} |
| 40 | Upper bounds from the symmetries | para | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | Two kinds of symmetry bound the functional dimension. The changes of b |
| 41 | Upper bounds from the symmetries | statement |  |  | \begin{restatable}[Upper bounds]{theorem}{thmUnlock}\label{thm:unlock} |
| 42 | Upper bounds from the symmetries | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 43 | Upper bounds from the symmetries | para |  |  | When the skipless and the residual network both satisfy it, each skip  |
| 44 | Upper bounds from the symmetries | statement | identifiable up to its symmetries, locally identifiable | identifiable up to its symmetries, locally identifiable | \begin{definition}[Identifiability up to symmetries]\label{def:ident}  |
| 45 | Upper bounds from the symmetries | para |  | analytic blocks | \para{Functional dimension and identifiability.} The two notions meet  |
| 46 | Upper bounds from the symmetries | para |  |  | \para{The gain in a transformer.} Under the equality condition, a resi |
| 47 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 48 | When the bounds are attained | para |  |  | The equality condition is a hypothesis, which can fail (\cref{sec:meas |
| 49 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for one block]{theorem}{thmOneBlock}\label |
| 50 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for residual networks at any depth]{theore |
| 51 | When the bounds are attained | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 52 | When the bounds are attained | para |  |  | \para{Proof sketches.} With one block, the parameters enter the functi |
| 53 | Residual and skipless networks compute different functions | para |  |  | \subsection{Residual and skipless networks compute different functions |
| 54 | Residual and skipless networks compute different functions | para |  |  | A family of functions cannot lie inside one of lower dimension, so for |
| 55 | Residual and skipless networks compute different functions | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 56 | Residual and skipless networks compute different functions | para |  |  | In (ii), each extra GELU unit adds $2\dm$ parameters against a gain of |
| 57 | Numerical ranks at depth, and a conjecture | para |  |  | \subsection{Numerical ranks at depth, and a conjecture}\label{sec:meas |
| 58 | Numerical ranks at depth, and a conjecture | para |  |  | At depth we compute the rank of the Jacobian on a large batch of input |
| 59 | Numerical ranks at depth, and a conjecture | float |  |  | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 60 | Numerical ranks at depth, and a conjecture | para |  |  | In two cases the measured rank stays below the upper bound. In skiples |
| 61 | Numerical ranks at depth, and a conjecture | statement |  |  | \begin{conjecture}[Equality without skips]\label{conj:equality} With o |
| 62 | Numerical ranks at depth, and a conjecture | para |  |  | For ReLU$^2$ and ReGLU blocks we expect the equality condition to hold |
| 63 | Numerical ranks at depth, and a conjecture | para |  |  | \para{One-hot tokens.} With one-hot tokens under RMSNorm, the rows of  |
| 64 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 65 | Conclusion | para |  |  | Skips tie the bases of all hidden states into one: a skipless network  |
| 66 | Conclusion | para |  |  | \para{Open questions.} The equality condition at depth is open for the |
| 67 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 68 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 69 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

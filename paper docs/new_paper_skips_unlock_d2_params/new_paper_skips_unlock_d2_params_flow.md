# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para |  | RMSNorm, change of basis, d_model, the width, functional dimension, per block, pre-RMSNorm | \begin{abstract} Skip connections change the function class of an MLP  |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro}\label{sec:related} |
| 2 | Introduction | para | d_model, the width |  | Skip connections are a building block of almost every deep network tra |
| 3 | Introduction | para |  | residual | Skipless networks are now trained as well. \citet{he2023shortcuts} tra |
| 4 | Introduction | para | L, the number of blocks | L, the number of blocks | \para{Where the degrees of freedom come from.} Without skips, the basi |
| 5 | Introduction | para | functional dimension | generic | \para{Functional dimension.} By the degrees of freedom of a network we |
| 6 | Introduction | float |  |  | \begin{figure}[t] \centering \includegraphics[width=0.94\linewidth]{fi |
| 7 | Introduction | para |  |  | \para{Functional dimension and equality of functions.} A set of functi |
| 8 | Introduction | para | A_l, a learned skip, identity skip, identity units, learned skip | A_l, a learned skip, identity skip, identity units, learned skip, readout / unembedding, redundancy | \para{Contributions and related work.} \Cref{tab:results} lists the re |
| 9 | Introduction | float | analytic blocks, functional dimension added by the skips | functional dimension added by the skips | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 10 | Setup | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, h, a hidden state, m, number of units, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, h, a hidden state, m, number of units, read / write (nouns) | \section{Setup}\label{sec:setup} \para{Blocks.} A hidden state is a ma |
| 11 | Setup | para | E and D, P, the number of parameters, per block, readout / unembedding, residual | E and D, P, the number of parameters | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 12 | Setup | para | N(h), RMSNorm, epsilon of RMSNorm, pre-RMSNorm, under rmsnorm | N(h), epsilon of RMSNorm, under rmsnorm | \para{Normalization.} RMSNorm, written $N$, divides each row $v$ of $h |
| 13 | Setup | para | generic |  | \para{Scope.} Networks have no biases, and their inputs are continuous |
| 14 | Skipless networks: one change of basis per hidden state | para |  |  | \section{Changes of basis that preserve the function}\label{sec:reduce |
| 15 | Skipless networks: one change of basis per hidden state | para | G, a change of basis, W, a generic weight matrix, change of basis | G, a change of basis, W, a generic weight matrix | Without normalization, nothing nonlinear happens between the write of  |
| 16 | Skipless networks: one change of basis per hidden state | statement | W_1, the chosen block | W_1, the chosen block | \begin{restatable}[Exact reduction without skips]{proposition}{propSki |
| 17 | Skipless networks: one change of basis per hidden state | para |  |  | Rows of a write work too: if $\dm$ rows of the write into $h_\ell$ for |
| 18 | Skipless networks: one change of basis per hidden state | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 19 | Learned skips: reduction to identity skips | para |  |  | \subsection{Learned skips: reduction to identity skips}\label{sec:lear |
| 20 | Learned skips: reduction to identity skips | para | Lambda | Lambda | A learned skip, which adds $hA$ in place of $h$, is a block of $\dm$ \ |
| 21 | Learned skips: reduction to identity skips | statement |  |  | \begin{restatable}[Learned skips reduce to identity skips]{theorem}{th |
| 22 | Learned skips: reduction to identity skips | para |  |  | So all $L\dm^2$ parameters of invertible learned skips can be removed, |
| 23 | Identity skips: one change of basis for the whole network | para |  |  | \subsection{Identity skips: one change of basis for the whole network} |
| 24 | Identity skips: one change of basis for the whole network | para |  |  | A residual network keeps one change of basis, the same at all its hidd |
| 25 | Identity skips: one change of basis for the whole network | statement |  |  | \begin{restatable}[One change of basis for the whole network]{theorem} |
| 26 | Identity skips: one change of basis for the whole network | para |  |  | So the $L$ skips remove $L\dm^2$ dimensions from this group, and \cref |
| 27 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \subsection{RMSNorm and LayerNorm: orthogonal changes of basis}\label{ |
| 28 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | With pre-RMSNorm, the network with learned skips computes \begin{equat |
| 29 | RMSNorm and LayerNorm: orthogonal changes of basis | statement |  |  | \begin{restatable}[Orthogonal changes of basis under RMSNorm]{theorem} |
| 30 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Learned skips under RMSNorm.} Under RMSNorm, part of a learned s |
| 31 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{LayerNorm.} LayerNorm is RMSNorm after a projection that removes |
| 32 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Trained models.}\label{sec:trained} The reduction applies to tra |
| 33 | Functional dimension with and without skips | para |  |  | \section{Functional dimension with and without skips}\label{sec:gain}  |
| 34 | Definition and a linear example | para |  |  | \subsection{Definition and a linear example}\label{sec:fd} |
| 35 | Definition and a linear example | statement | F_theta, redundancy | F_theta | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 36 | Definition and a linear example | para |  |  | A continuous symmetry adds to the redundancy: if a continuous family o |
| 37 | Definition and a linear example | para |  |  | \begin{example}[A product of three matrices]\label{ex:three} The linea |
| 38 | Upper bounds from the symmetries | para |  |  | \subsection{Upper bounds from the symmetries}\label{sec:count} |
| 39 | Upper bounds from the symmetries | para | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | Two kinds of symmetry bound the functional dimension. The changes of b |
| 40 | Upper bounds from the symmetries | statement |  |  | \begin{restatable}[Upper bounds]{theorem}{thmUnlock}\label{thm:unlock} |
| 41 | Upper bounds from the symmetries | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 42 | Upper bounds from the symmetries | para |  |  | When the residual network satisfies it, each skip unlocks $\dim\G$ par |
| 43 | Upper bounds from the symmetries | statement | identifiable up to its symmetries, locally identifiable | identifiable up to its symmetries, locally identifiable | \begin{definition}[Identifiability up to symmetries]\label{def:ident}  |
| 44 | Upper bounds from the symmetries | para |  | analytic blocks | \para{Functional dimension and identifiability.} The two notions meet  |
| 45 | Upper bounds from the symmetries | para |  |  | \para{The gain in a transformer.} Under the equality condition, a resi |
| 46 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 47 | When the bounds are attained | para |  |  | The equality condition is a hypothesis, and it can fail (\cref{sec:mea |
| 48 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for one block]{theorem}{thmOneBlock}\label |
| 49 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for residual networks at any depth]{theore |
| 50 | When the bounds are attained | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 51 | When the bounds are attained | para |  |  | \para{Proof sketches.} With one block, the parameters enter the functi |
| 52 | Residual and skipless networks compute different functions | para |  |  | \subsection{Residual and skipless networks compute different functions |
| 53 | Residual and skipless networks compute different functions | para |  |  | A set of functions cannot lie inside a set of lower dimension, so for  |
| 54 | Residual and skipless networks compute different functions | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 55 | Residual and skipless networks compute different functions | para |  |  | In (ii), each extra GELU unit adds $2\dm$ parameters against a gain of |
| 56 | Numerical ranks at depth, and a conjecture | para |  |  | \subsection{Numerical ranks at depth, and a conjecture}\label{sec:meas |
| 57 | Numerical ranks at depth, and a conjecture | para |  |  | At depth we compute the rank of the Jacobian on a large batch of input |
| 58 | Numerical ranks at depth, and a conjecture | float |  |  | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 59 | Numerical ranks at depth, and a conjecture | para |  |  | In two cases the measured rank stays below the upper bound. In skiples |
| 60 | Numerical ranks at depth, and a conjecture | statement |  |  | \begin{conjecture}[Equality without skips]\label{conj:equality} With o |
| 61 | Numerical ranks at depth, and a conjecture | para |  |  | For ReLU$^2$ and ReGLU blocks we expect the equality condition to hold |
| 62 | Numerical ranks at depth, and a conjecture | para |  |  | \para{One-hot tokens.} With one-hot tokens under RMSNorm, the rows of  |
| 63 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 64 | Conclusion | para |  |  | Skip connections change how a network uses its parameters. Without ski |
| 65 | Conclusion | para |  |  | \para{Open questions.} The equality condition at depth is open for the |
| 66 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 67 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 68 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

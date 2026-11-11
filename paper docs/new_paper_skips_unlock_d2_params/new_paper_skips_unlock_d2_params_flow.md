# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para |  | RMSNorm, d_model, the width, functional dimension, per block, pre-RMSNorm | \begin{abstract} Skip connections change the function class of an MLP  |
| 1 | abstract | float | L, the number of blocks, d_hidden, the number of hidden units | L, the number of blocks, d_hidden, the number of hidden units | \begin{figure}[!h] \centering \includegraphics[width=0.94\linewidth]{f |
| 2 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 3 | Introduction | para | d_model, the width |  | Skip connections are a building block of almost every deep network tra |
| 4 | Introduction | para |  | residual | Skipless networks have recently been trained to varying degrees of suc |
| 5 | Introduction | para |  | change of basis, readout / unembedding | \para{Where the degrees of freedom come from.} Without skips, the basi |
| 6 | Introduction | para | functional dimension | generic | \para{Functional dimension.} By the degrees of freedom of a network we |
| 7 | Contributions | para |  |  | \subsection{Contributions}\label{sec:contributions} |
| 8 | Contributions | para | analytic blocks |  | \para{Main result.} Residual networks attain the upper bound from the  |
| 9 | Contributions | para | A_l, a learned skip, identity skip, learned skip, locally identifiable | A_l, a learned skip, analytic blocks, identity skip, learned skip, locally identifiable | \para{Further results.} \Cref{tab:results} lists the proven counts, an |
| 10 | Contributions | float | functional dimension added by the skips | functional dimension added by the skips | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 11 | Related work | para |  |  | \subsection{Related work}\label{sec:related} |
| 12 | Related work | para |  |  | \para{The change of basis as a symmetry.} \citet{zhao2023symmetries} f |
| 13 | Related work | para |  |  | \para{One change of basis for a residual network.} Earlier work uses o |
| 14 | Related work | para |  |  | \para{Learned and emulated skips.} LAuReL trains skips that are the id |
| 15 | Related work | para |  |  | \para{Functional dimension and the Jacobian.} \citet{grigsby2022functi |
| 16 | Related work | para |  | redundancy | \para{Identifiability and the symmetries of attention.} For attention  |
| 17 | Setup | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, h, a hidden state, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, h, a hidden state, read / write (nouns) | \section{Setup}\label{sec:setup} \para{Blocks.} A hidden state is a ma |
| 18 | Setup | para | E and D, P, the number of parameters, per block, readout / unembedding, residual | E and D, P, the number of parameters | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 19 | Setup | para | epsilon of RMSNorm, pre-RMSNorm, under rmsnorm | epsilon of RMSNorm, under rmsnorm | \para{Normalization.} RMSNorm with the constant $\varepsilon > 0$ is t |
| 20 | Setup | para | generic |  | \para{Scope.} Networks have no biases, and their inputs are continuous |
| 21 | Changes of basis that preserve the function | para |  |  | \section{Changes of basis that preserve the function}\label{sec:reduce |
| 22 | Changes of basis that preserve the function | para | G, a change of basis | G, a change of basis | The results of this section rest on one symmetry, which the first two  |
| 23 | Changes of basis that preserve the function | statement | W, a generic weight matrix, change of basis | W, a generic weight matrix | \begin{definition}[Change of basis]\label{def:cob} In a skipless and i |
| 24 | Changes of basis that preserve the function | para |  |  | \citet{zhao2023symmetries} formalize this symmetry for MLPs. It adapts |
| 25 | Changes of basis that preserve the function | para |  |  | The computation \eqref{eq:product} uses only the form \eqref{eq:block} |
| 26 | Skipless networks: one change of basis per hidden state | para |  |  | \subsection{Skipless networks: one change of basis per hidden state}\l |
| 27 | Skipless networks: one change of basis per hidden state | para |  |  | In a skipless network without normalization, the invariance \eqref{eq: |
| 28 | Skipless networks: one change of basis per hidden state | statement | W_1, the chosen block | W_1, the chosen block | \begin{restatable}[Exact reduction without skips]{proposition}{propSki |
| 29 | Skipless networks: one change of basis per hidden state | para |  |  | Rows of a write work too: if $\dm$ rows of the write into $h_\ell$ ($\ |
| 30 | Skipless networks: one change of basis per hidden state | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 31 | Residual blocks as skipless ones | para |  |  | \subsection{Residual blocks as skipless ones}\label{sec:learned} |
| 32 | Residual blocks as skipless ones | para | Lambda, identity units | Lambda, identity units | In this subsection we write a block together with its learned skip as  |
| 33 | Residual blocks as skipless ones | statement |  |  | \begin{restatable}[Learned skips reduce to identity skips]{theorem}{th |
| 34 | Residual blocks as skipless ones | para |  |  | So the networks with invertible learned skips have $L\dm^2$ more param |
| 35 | Identity skips: one change of basis for the whole network | para |  |  | \subsection{Identity skips: one change of basis for the whole network} |
| 36 | Identity skips: one change of basis for the whole network | para |  |  | A residual network keeps one change of basis, the same at all its hidd |
| 37 | Identity skips: one change of basis for the whole network | statement |  |  | \begin{restatable}[One change of basis for the whole network]{theorem} |
| 38 | Identity skips: one change of basis for the whole network | para |  |  | So the $L$ skips remove $L\dm^2$ dimensions from this group, and \cref |
| 39 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \subsection{RMSNorm and LayerNorm: orthogonal changes of basis}\label{ |
| 40 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | With pre-RMSNorm, the network with learned skips computes \begin{equat |
| 41 | RMSNorm and LayerNorm: orthogonal changes of basis | statement |  |  | \begin{restatable}[Orthogonal changes of basis under RMSNorm]{theorem} |
| 42 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Learned skips under RMSNorm.} In \eqref{eq:prenorm} the skip $A_ |
| 43 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{LayerNorm.} LayerNorm is RMSNorm after a projection that removes |
| 44 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Trained models.}\label{sec:trained} The reduction applies to tra |
| 45 | Functional dimension with and without skips | para |  |  | \section{Functional dimension with and without skips}\label{sec:gain}  |
| 46 | Definition and a linear example | para |  |  | \subsection{Definition and a linear example}\label{sec:fd} |
| 47 | Definition and a linear example | statement | F_theta, redundancy | F_theta | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 48 | Definition and a linear example | para |  |  | A continuous symmetry adds to the redundancy: if a continuous family o |
| 49 | Definition and a linear example | para |  |  | \begin{example}[Not all reductions are maximal]\label{ex:three} The li |
| 50 | Definition and a linear example | para |  |  | \begin{example}[Fewer degrees of freedom than stored entries]\label{ex |
| 51 | Upper bounds from the symmetries | para |  |  | \subsection{Upper bounds from the symmetries}\label{sec:count} |
| 52 | Upper bounds from the symmetries | para | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | Two kinds of symmetry bound the functional dimension. The changes of b |
| 53 | Upper bounds from the symmetries | statement |  |  | \begin{restatable}[Upper bounds]{theorem}{thmUnlock}\label{thm:unlock} |
| 54 | Upper bounds from the symmetries | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 55 | Upper bounds from the symmetries | para |  |  | When the residual network satisfies it, each skip unlocks $\dim\G$ par |
| 56 | Upper bounds from the symmetries | statement | identifiable up to its symmetries | identifiable up to its symmetries | \begin{definition}[Identifiability up to symmetries]\label{def:ident}  |
| 57 | Upper bounds from the symmetries | para |  |  | \citet{vlacic2020affine} define identifiability up to an equivalence r |
| 58 | Upper bounds from the symmetries | para |  |  | \para{Functional dimension and identifiability.} The two notions meet  |
| 59 | Upper bounds from the symmetries | para |  |  | \para{The gain in a transformer.} Under the equality condition, a resi |
| 60 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 61 | When the bounds are attained | para |  |  | The equality condition is a hypothesis, and it can fail (\cref{sec:mea |
| 62 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for one block]{theorem}{thmOneBlock}\label |
| 63 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for residual networks at any depth]{theore |
| 64 | When the bounds are attained | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 65 | When the bounds are attained | para |  |  | \para{Proof sketches.} With one block, the parameters enter the functi |
| 66 | Residual and skipless networks compute different functions | para |  |  | \subsection{Residual and skipless networks compute different functions |
| 67 | Residual and skipless networks compute different functions | statement | pointwise limit | pointwise limit | \begin{definition*}[Pointwise limit] Let $\mathcal X = \R^{T\times d_{ |
| 68 | Residual and skipless networks compute different functions | para |  |  | If a sequence of networks of $\mathcal F$ converges to $F$ at every in |
| 69 | Residual and skipless networks compute different functions | para | definable in an o-minimal structure | definable in an o-minimal structure | By \cref{def:fd,thm:resdepth}, the Jacobian of the residual network ha |
| 70 | Residual and skipless networks compute different functions | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 71 | Residual and skipless networks compute different functions | para |  |  | For GELU blocks without normalization, \citet{mijoski2026worth} show t |
| 72 | Numerical ranks at depth, and a conjecture | para |  |  | \subsection{Numerical ranks at depth, and a conjecture}\label{sec:meas |
| 73 | Numerical ranks at depth, and a conjecture | para |  |  | At depth we compute the rank of the Jacobian on a large batch of input |
| 74 | Numerical ranks at depth, and a conjecture | float |  |  | \begin{table}[b] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 75 | Numerical ranks at depth, and a conjecture | para |  |  | In two cases the measured rank stays below the upper bound. In skiples |
| 76 | Numerical ranks at depth, and a conjecture | statement |  |  | \begin{conjecture}[Equality without skips]\label{conj:equality} With o |
| 77 | Numerical ranks at depth, and a conjecture | para |  |  | For ReLU$^2$ and ReGLU blocks we expect the equality condition to hold |
| 78 | Numerical ranks at depth, and a conjecture | para |  |  | \para{One-hot tokens.} With one-hot tokens under RMSNorm, the rows of  |
| 79 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 80 | Conclusion | para |  |  | Skip connections change how a network uses its parameters. Without ski |
| 81 | Conclusion | para |  |  | \para{Open questions.} The equality condition at depth is open for the |
| 82 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 83 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 84 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

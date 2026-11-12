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
| 9 | Contributions | para | A_l, a learned skip, identity skip, learned skip, locally identifiable | A_l, a learned skip, analytic blocks, identity skip, learned skip, locally identifiable | \begin{enumerate}[label=\arabic*.] \item \textit{Changes of basis, in  |
| 10 | Contributions | float | ReLU squared, functional dimension added by the skips | ReLU squared, functional dimension added by the skips | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 11 | Related work | para |  |  | \subsection{Related work}\label{sec:related} |
| 12 | Related work | para |  |  | \para{The change of basis as a symmetry.} \citet{godfrey2022symmetries |
| 13 | Related work | para |  |  | \para{One change of basis for a residual network.} Earlier work uses o |
| 14 | Related work | para |  |  | \para{Learned and emulated skips.} LAuReL trains skips that are the id |
| 15 | Related work | para |  |  | \para{Functional dimension and the Jacobian.} \citet{grigsby2022functi |
| 16 | Related work | para |  |  | \para{Identifiability and the symmetries of attention.} For skipless n |
| 17 | Setup | para |  |  | \section{Setup}\label{sec:setup} This section fixes the networks that  |
| 18 | Setup | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, T, number of tokens, gated block, h, a hidden state, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, T, number of tokens, gated block, h, a hidden state, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 19 | Setup | para | E and D, P, the number of parameters, per block, readout / unembedding, residual | E and D, P, the number of parameters | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 20 | Setup | para | epsilon of RMSNorm, pre-RMSNorm, under rmsnorm | epsilon of RMSNorm, under rmsnorm | \para{Normalization.} RMSNorm with the constant $\varepsilon > 0$ is t |
| 21 | Setup | para | generic |  | \para{Scope.} Networks have no biases, and their inputs are continuous |
| 22 | Changes of basis that preserve the function | para |  |  | \section{Changes of basis that preserve the function}\label{sec:reduce |
| 23 | Changes of basis that preserve the function | para | G, a change of basis | G, a change of basis | The results of this section rest on one symmetry, which the first two  |
| 24 | Changes of basis that preserve the function | statement | W, a generic weight matrix, change of basis | W, a generic weight matrix | \begin{definition}[Change of basis]\label{def:cob} In a skipless and i |
| 25 | Changes of basis that preserve the function | para |  |  | \para{What is known.} This section builds on results that are known, i |
| 26 | Changes of basis that preserve the function | para |  |  | \para{What this section builds.} We use the symmetry to remove paramet |
| 27 | Skipless networks: one change of basis per hidden state | para |  |  | \subsection{Skipless networks: one change of basis per hidden state}\l |
| 28 | Skipless networks: one change of basis per hidden state | para |  |  | We start with networks that have neither skips nor normalization, wher |
| 29 | Skipless networks: one change of basis per hidden state | para |  |  | In a skipless network without normalization, the invariance \eqref{eq: |
| 30 | Skipless networks: one change of basis per hidden state | para | W_1, the chosen block | W_1, the chosen block | \begin{example*}[Choosing the submatrix] Take $1 \le \ell < L$ and wri |
| 31 | Skipless networks: one change of basis per hidden state | statement |  |  | \begin{restatable}[Exact reduction without skips]{proposition}{propSki |
| 32 | Skipless networks: one change of basis per hidden state | para |  |  | Rows of the matrix $\Wwrite^{\ell}$ work too, or rows of $E$ if $\ell  |
| 33 | Skipless networks: one change of basis per hidden state | para |  |  | \begin{example}[Choosing rows]\label{ex:rows} Let $\dm = 2$ and $\dhid |
| 34 | Skipless networks: one change of basis per hidden state | para |  |  | Take an attention block $B_\ell$ of a skipless transformer with $Hd_h  |
| 35 | Skipless networks: one change of basis per hidden state | float |  |  | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 36 | Telescoping (generic) learned skips to identity skips | para |  |  | \subsection{Telescoping (generic) learned skips to identity skips}\lab |
| 37 | Telescoping (generic) learned skips to identity skips | para |  |  | In \cref{sec:skipless} the change of basis at each hidden state was ch |
| 38 | Telescoping (generic) learned skips to identity skips | para |  |  | The skip $A_\ell$ multiplies $h_{\ell-1}$, and the result is added to  |
| 39 | Telescoping (generic) learned skips to identity skips | para | Lambda | Lambda | Let every $A_\ell$ be invertible, as it is at generic parameters. The  |
| 40 | Telescoping (generic) learned skips to identity skips | statement |  |  | \begin{restatable}[Learned skips reduce to identity skips]{theorem}{th |
| 41 | Telescoping (generic) learned skips to identity skips | para |  |  | So the networks with invertible learned skips have $L\dm^2$ more param |
| 42 | Telescoping (generic) learned skips to identity skips | statement |  |  | \begin{remark}[The reduction is not unique]\label{rem:notunique} In a  |
| 43 | Identity skips: one change of basis for the whole network | para |  |  | \subsection{Identity skips: one change of basis for the whole network} |
| 44 | Identity skips: one change of basis for the whole network | para |  |  | \Cref{sec:learned} turned invertible learned skips into identity skips |
| 45 | Identity skips: one change of basis for the whole network | para |  |  | A residual network keeps one change of basis, the same at all its hidd |
| 46 | Identity skips: one change of basis for the whole network | statement |  |  | \begin{restatable}[One change of basis for the whole network]{theorem} |
| 47 | Identity skips: one change of basis for the whole network | para |  |  | So the $L$ skips remove $L\dm^2$ dimensions from this group, and \cref |
| 48 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \subsection{RMSNorm and LayerNorm: orthogonal changes of basis}\label{ |
| 49 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | Up to here the networks had no normalization. We now add pre-RMSNorm a |
| 50 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | With pre-RMSNorm, the network with learned skips computes \begin{equat |
| 51 | RMSNorm and LayerNorm: orthogonal changes of basis | statement |  |  | \begin{restatable}[Orthogonal changes of basis under RMSNorm]{theorem} |
| 52 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Learned skips under RMSNorm.} In \eqref{eq:prenorm} the skip $A_ |
| 53 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{LayerNorm.} LayerNorm is RMSNorm after a projection that removes |
| 54 | RMSNorm and LayerNorm: orthogonal changes of basis | para |  |  | \para{Trained models.}\label{sec:trained} The reduction applies to tra |
| 55 | Functional dimension with and without skips | para |  | redundancy | \section{Functional dimension with and without skips}\label{sec:gain}  |
| 56 | Definition and a linear example | para |  |  | \subsection{Definition and a linear example}\label{sec:fd} |
| 57 | Definition and a linear example | para |  |  | We first define the functional dimension and the redundancy, and compu |
| 58 | Definition and a linear example | statement | F_theta, redundancy | F_theta | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 59 | Definition and a linear example | para |  |  | A continuous symmetry adds to the redundancy: if a continuous family o |
| 60 | Definition and a linear example | para |  |  | \begin{example}[Not all reductions are maximal]\label{ex:three} The li |
| 61 | Definition and a linear example | para |  |  | \begin{example}[Fewer degrees of freedom than stored entries]\label{ex |
| 62 | Upper bounds from the symmetries | para |  |  | \subsection{Upper bounds from the symmetries}\label{sec:count} |
| 63 | Upper bounds from the symmetries | para |  |  | We now bound the functional dimension from above. A direction in which |
| 64 | Upper bounds from the symmetries | para | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | s, symmetries inside, script G, symmetries inside blocks, symmetries inside the blocks | Two kinds of symmetry bound the functional dimension. The changes of b |
| 65 | Upper bounds from the symmetries | statement |  |  | \begin{restatable}[Upper bounds]{theorem}{thmUnlock}\label{thm:unlock} |
| 66 | Upper bounds from the symmetries | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 67 | Upper bounds from the symmetries | para |  |  | When the residual network satisfies it, each skip unlocks $\dim\G$ par |
| 68 | Upper bounds from the symmetries | statement | identifiable up to its symmetries | identifiable up to its symmetries | \begin{definition}[Identifiability up to symmetries]\label{def:ident}  |
| 69 | Upper bounds from the symmetries | para |  |  | \citet{vlacic2020affine} define identifiability up to an equivalence r |
| 70 | Upper bounds from the symmetries | para |  |  | \para{Functional dimension and identifiability.} The equality conditio |
| 71 | Upper bounds from the symmetries | statement |  |  | \begin{restatable}[The equality condition and local identifiability]{p |
| 72 | Upper bounds from the symmetries | para |  |  | The proposition compares only parameters that are close to each other. |
| 73 | Upper bounds from the symmetries | para |  |  | \para{The gain in a transformer.} Under the equality condition, a resi |
| 74 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 75 | When the bounds are attained | para |  |  | The equality condition is a hypothesis, and it can fail (\cref{sec:mea |
| 76 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for one block]{theorem}{thmOneBlock}\label |
| 77 | When the bounds are attained | statement |  |  | \begin{remark*}[One attention block without a skip] For an attention b |
| 78 | When the bounds are attained | para |  |  | At generic parameters, $\Xi_i$ and $\Psi_i$ are products of two factor |
| 79 | When the bounds are attained | statement |  |  | \begin{restatable}[Equality for residual networks at any depth]{theore |
| 80 | When the bounds are attained | para |  |  | \begin{corollary}[Residual networks are locally identifiable]\label{co |
| 81 | When the bounds are attained | para |  |  | This is \cref{thm:resdepth} together with \cref{prop:localid}. Whether |
| 82 | When the bounds are attained | para |  |  | \begin{corollary}[Attention blocks without embedding and readout]\labe |
| 83 | When the bounds are attained | para |  |  | \citet{henry2026generic} proves this formula for one block without a s |
| 84 | When the bounds are attained | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 85 | When the bounds are attained | para |  |  | By \cref{prop:localid}, the skipless networks of \cref{thm:exactgain}  |
| 86 | When the bounds are attained | para |  |  | \para{Proof sketches.} With one block, the parameters enter the functi |
| 87 | Residual and skipless networks compute different functions | para |  |  | \subsection{Residual and skipless networks compute different functions |
| 88 | Residual and skipless networks compute different functions | para |  |  | The gain in functional dimension says something about the functions th |
| 89 | Residual and skipless networks compute different functions | statement | pointwise limit | pointwise limit | \begin{definition*}[Pointwise limit] Let $\mathcal X = \R^{T\times d_{ |
| 90 | Residual and skipless networks compute different functions | para |  |  | If a sequence of networks of $\mathcal F$ converges to $F$ at every in |
| 91 | Residual and skipless networks compute different functions | para | definable in an o-minimal structure | definable in an o-minimal structure | By \cref{def:fd,thm:resdepth}, the Jacobian of the residual network ha |
| 92 | Residual and skipless networks compute different functions | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 93 | Residual and skipless networks compute different functions | para |  |  | For GELU blocks without normalization, \citet{mijoski2026worth} show t |
| 94 | Numerical ranks at depth, and a conjecture | para |  |  | \subsection{Numerical ranks at depth, and a conjecture}\label{sec:meas |
| 95 | Numerical ranks at depth, and a conjecture | para |  |  | For skipless networks at depth, \cref{thm:exactgain} gives the equalit |
| 96 | Numerical ranks at depth, and a conjecture | para |  |  | At depth we compute the rank of the Jacobian on a large batch of input |
| 97 | Numerical ranks at depth, and a conjecture | float |  |  | \begin{table}[b] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 98 | Numerical ranks at depth, and a conjecture | para |  |  | In two cases the measured rank stays below the upper bound. In skiples |
| 99 | Numerical ranks at depth, and a conjecture | statement |  |  | \begin{conjecture}[Equality without skips]\label{conj:equality} With o |
| 100 | Numerical ranks at depth, and a conjecture | para |  |  | The analogue of the conjecture is known for polynomial activations. \c |
| 101 | Numerical ranks at depth, and a conjecture | para |  |  | \para{One-hot tokens.} With one-hot tokens under RMSNorm, the rows of  |
| 102 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 103 | Conclusion | para |  |  | Skip connections change how a network uses its parameters. Without ski |
| 104 | Conclusion | para |  |  | \para{Open questions.} The equality condition at depth is open for the |
| 105 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 106 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 107 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

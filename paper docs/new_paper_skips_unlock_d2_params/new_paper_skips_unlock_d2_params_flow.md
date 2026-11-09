# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | d_model, the width, functional dimension | RMSNorm, change of basis, d_model, the width, functional dimension, per block, redundancy, residual | \begin{abstract} Residual and skipless networks with the same blocks h |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para |  |  | Skip connections are a building block of almost every deep network tra |
| 3 | Introduction | para | RMSNorm, epsilon of RMSNorm, identity skip, pre-RMSNorm, readout / unembedding | epsilon of RMSNorm, identity skip, pre-RMSNorm, readout / unembedding | So what do skips change, besides training? A residual network adds the |
| 4 | Introduction | para | G, a change of basis, W, a generic weight matrix, h, a hidden state | G, a change of basis, h, a hidden state | \para{Hidden states have units.} Think of the coordinates of a hidden  |
| 5 | Introduction | para | L, the number of blocks | L, the number of blocks | \para{Free bases are removable parameters.} Each such $G$ can be spent |
| 6 | Introduction | para | P, the number of parameters, running example | P, the number of parameters, running example | \para{Fewer parameters, the same functions.} For almost every choice o |
| 7 | Introduction | para |  |  | \para{Known symmetries.} Permuting the hidden units or heads of a bloc |
| 8 | Introduction | float |  |  | \begin{figure}[t] \centering \includegraphics[width=0.94\linewidth]{fi |
| 9 | Introduction | para | A_l, a learned skip, exact reduction, identity units, learned skip, learned skips are identity units, one change of basis is left, skips unlock functional dimension | A_l, a learned skip, exact reduction, identity units, learned skip, learned skips are identity units, one change of basis is left, skips unlock functional dimension | \para{Contributions.} \begin{enumerate}[label=\arabic*.] \item \emph{E |
| 10 | Introduction | float | functional dimension added by the skips, smooth blocks | functional dimension added by the skips, generic, smooth blocks | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 11 | Setup | para |  |  | \section{Setup}\label{sec:setup} \takeaway{A block reads a hidden stat |
| 12 | Setup | para | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | B, the map of a block, B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 13 | Setup | para | E and D, per block, residual | E and D | \para{Networks.} A network maps an input $x \in \R^{T\times d_{\mathrm |
| 14 | Setup | para | N(h) | N(h) | \para{Normalization.} In a \emph{pre-RMSNorm} network the blocks and t |
| 15 | Setup | para | generic |  | \para{Scope.} For simplicity, networks have no biases. Every MLP block |
| 16 | Free changes of basis remove parameters exactly | para |  |  | \section{Free changes of basis remove parameters exactly}\label{sec:re |
| 17 | Without skips: one free submatrix per hidden state | para |  |  | \subsection{Without skips: one free submatrix per hidden state}\label{ |
| 18 | Without skips: one free submatrix per hidden state | para | change of basis | W, a generic weight matrix | Without normalization, nothing nonlinear happens between the write of  |
| 19 | Without skips: one free submatrix per hidden state | para |  |  | A symmetry can be spent. |
| 20 | Without skips: one free submatrix per hidden state | statement | W_1, the chosen block | W_1, the chosen block | \begin{restatable}[One free submatrix per hidden state]{proposition}{p |
| 21 | Without skips: one free submatrix per hidden state | para |  |  | Rows of a write work too: if $\dm$ rows of the write into $h_\ell$ for |
| 22 | Without skips: one free submatrix per hidden state | para |  |  | So skipless networks with one identity submatrix per hidden state comp |
| 23 | Without skips: one free submatrix per hidden state | float | U and V | U and V | \begin{figure}[t] \centering [a TikZ drawing, omitted here; the captio |
| 24 | Learned skips are blocks of identity units | para |  |  | \subsection{Learned skips are blocks of identity units}\label{sec:lear |
| 25 | Learned skips are blocks of identity units | para |  |  | A learned skip, which adds $hA$ in place of $h$, is a block in disguis |
| 26 | Learned skips are blocks of identity units | para |  |  | \para{Merge.} Nothing nonlinear happens between $U$ and $V$, so the id |
| 27 | Learned skips are blocks of identity units | para | Lambda | Lambda | \para{Reduce.} The skip $A_\ell$ reads $h_{\ell-1}$ and writes $h_\ell |
| 28 | Learned skips are blocks of identity units | statement |  |  | \begin{restatable}[Learned skips are identity skips]{theorem}{thmLearn |
| 29 | Learned skips are blocks of identity units | para |  |  | So all $L\dm^2$ parameters of the learned skips can go: without normal |
| 30 | Identity skips tie the hidden states | para |  |  | \subsection{Identity skips tie the hidden states}\label{sec:global}\la |
| 31 | Identity skips tie the hidden states | para |  |  | After the sweep one change of basis is left, and it must be the same a |
| 32 | Identity skips tie the hidden states | statement |  |  | \begin{restatable}[One change of basis is left]{theorem}{thmTie}\label |
| 33 | Identity skips tie the hidden states | para |  |  | So the $L$ skips remove $L\dm^2$ dimensions of symmetry. In the langua |
| 34 | Identity skips tie the hidden states | para |  |  | \para{A counterexample.} \citet[Theorem~7]{wang2025gauge} state that t |
| 35 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | \subsection{Under RMSNorm: orthogonal maps pass, triangles stay}\label |
| 36 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | With pre-RMSNorm, the network with learned skips computes \begin{equat |
| 37 | Under RMSNorm: orthogonal maps pass, triangles stay | statement |  |  | \begin{restatable}[Triangles under RMSNorm]{theorem}{thmRMSTri}\label{ |
| 38 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | \para{What a learned skip carries.} Write a skip as an upper triangula |
| 39 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | LayerNorm is RMSNorm after a projection that removes the mean of each  |
| 40 | What trained models give up | para |  |  | \subsection{What trained models give up}\label{sec:trained} |
| 41 | What trained models give up | para |  |  | \para{A skipless ViT-B.} The skipless ViT-B of \citet{ji2026cutting} h |
| 42 | What trained models give up | para |  |  | \para{Llama-3.1.} A pre-RMSNorm language model with an untied readout  |
| 43 | Fewer parameters is not fewer functions | para |  |  | \section{Fewer parameters is not fewer functions}\label{sec:gain} \tak |
| 44 | Functional dimension | para |  |  | \subsection{Functional dimension}\label{sec:fd} |
| 45 | Functional dimension | para | F_theta, redundancy | F_theta | \para{Functional dimension.} Let $F_\theta$ be the function computed a |
| 46 | Functional dimension | para |  |  | \para{Three matrices, one map.} The linear network $x \mapsto xM_1M_2M |
| 47 | What the skips unlock | para |  |  | \subsection{What the skips unlock}\label{sec:count} |
| 48 | What the skips unlock | para | s, symmetries inside, script G, symmetries inside blocks | s, symmetries inside, script G, symmetries inside blocks | Blocks also have \emph{symmetries inside}, which leave the hidden stat |
| 49 | What the skips unlock | statement |  |  | \begin{restatable}[What the skips unlock]{theorem}{thmUnlock}\label{th |
| 50 | What the skips unlock | para | equality condition | equality condition | A network satisfies the \emph{equality condition} if its bound in \cre |
| 51 | What the skips unlock | para |  |  | \para{Learned skips.} A network with learned skips has $P + L\dm^2$ pa |
| 52 | What the skips unlock | para |  |  | \para{At equal parameter count.} Under the equality condition, a resid |
| 53 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 54 | When the bounds are attained | para |  |  | The equality condition is a hypothesis. We prove it in three cases. |
| 55 | When the bounds are attained | statement |  |  | \begin{restatable}[One block]{theorem}{thmOneBlock}\label{thm:oneblock |
| 56 | When the bounds are attained | statement |  |  | \begin{restatable}[Residual networks at any depth]{theorem}{thmResDept |
| 57 | When the bounds are attained | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 58 | When the bounds are attained | para |  |  | \para{How the proofs go.} With one block, the parameters enter the fun |
| 59 | Measured at depth | para |  |  | \subsection{Measured at depth}\label{sec:measured} |
| 60 | Measured at depth | para |  |  | For deeper networks we compute the rank of the Jacobian on a large bat |
| 61 | Measured at depth | float |  |  | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 62 | Measured at depth | para |  |  | In two cases the measured rank stays below the upper bound. Under RMSN |
| 63 | Measured at depth | statement |  |  | \begin{conjecture}[Equality condition]\label{conj:equality} With or wi |
| 64 | Measured at depth | para |  |  | For smooth blocks, \cref{thm:resdepth} proves the residual half of the |
| 65 | A gap that separates function classes | para |  |  | \subsection{A gap that separates function classes}\label{sec:classes} |
| 66 | A gap that separates function classes | para |  |  | For smooth blocks, the gap in functional dimension keeps the two class |
| 67 | A gap that separates function classes | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 68 | A gap that separates function classes | para |  |  | Part (i) covers attention networks, and in (ii) each extra GELU unit a |
| 69 | Related work | para |  |  | \section{Related work}\label{sec:related} |
| 70 | Related work | para |  |  | \para{Absorbing the skip.} Without normalization, $\dm$ more ReLU or G |
| 71 | Related work | para |  |  | \para{Changes of basis at hidden layers.} \citet{zhao2023symmetries} d |
| 72 | Related work | para |  |  | \para{Removing weights.} Changes of basis can set the values and proje |
| 73 | Related work | para |  |  | \para{The basis of the residual stream.} The residual stream has no pr |
| 74 | Related work | para |  |  | \para{Symmetries and residual networks in theory.} \citet{wang2025gaug |
| 75 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 76 | Conclusion | para |  |  | Skips tie the bases of all hidden states into one. A skipless network  |
| 77 | Conclusion | para |  |  | \para{Open questions.} The equality condition at depth is open for ski |
| 78 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 79 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 80 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | d_model, the width, functional dimension | change of basis, d_model, the width, functional dimension, per block, redundancy, residual | \begin{abstract} Residual and skipless networks with the same blocks h |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para |  |  | Skip connections are a building block of almost every deep network tra |
| 3 | Introduction | para | RMSNorm and its epsilon, h, a hidden state, identity skip, pre-RMSNorm, readout / unembedding | RMSNorm and its epsilon, h, a hidden state, identity skip, pre-RMSNorm, readout / unembedding | So what do skips change, besides training? A residual network adds the |
| 4 | Introduction | para | G, a change of basis, W, a generic weight matrix | G, a change of basis | \para{Hidden states have units.} Think of the coordinates of a hidden  |
| 5 | Introduction | para | L, the number of blocks | L, the number of blocks | \para{Free units are removable parameters.} Each such $G$ can be spent |
| 6 | Introduction | para | P, the number of parameters, running example | P, the number of parameters, running example | \para{Fewer parameters, the same functions.} Removing these parameters |
| 7 | Introduction | para |  |  | \para{Known symmetries.} Permuting the hidden units or the heads of a  |
| 8 | Introduction | float |  |  | \begin{figure}[t] \centering \includegraphics[width=0.94\linewidth]{fi |
| 9 | Introduction | para | A_l, a learned skip, exact reduction, identity units, learned skip, learned skips are identity units, one change of basis is left, skips unlock functional dimension | A_l, a learned skip, exact reduction, identity units, learned skip, learned skips are identity units, one change of basis is left, skips unlock functional dimension | \para{Contributions.} \begin{enumerate}[label=\arabic*.] \item \emph{E |
| 10 | Introduction | float | functional dimension added by the skips, smooth blocks | functional dimension added by the skips, generic, smooth blocks | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \n |
| 11 | Setup | para |  |  | \section{Setup}\label{sec:setup} \takeaway{A block reads a hidden stat |
| 12 | Setup | para | B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | B_theta, Wread, Wwrite, theta, H and d_h, ReLU squared, T, number of tokens, gated block, m, number of units, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 13 | Setup | para | E and D, per block, residual | E and D | \para{Networks.} Every network starts with a linear embedding $E \in \ |
| 14 | Setup | para | N(h) | N(h) | \para{Normalization.} In a \emph{pre-RMSNorm} network the blocks and t |
| 15 | Setup | para | generic |  | \para{Scope.} For simplicity, networks have no biases. Every MLP block |
| 16 | Free changes of basis remove parameters exactly | para |  |  | \section{Free changes of basis remove parameters exactly}\label{sec:re |
| 17 | Free changes of basis remove parameters exactly | para |  |  | \Cref{sec:skipless,sec:learned,sec:global} assume no normalization; \c |
| 18 | Without skips: one free submatrix per hidden state | para |  |  | \subsection{Without skips: one free submatrix per hidden state}\label{ |
| 19 | Without skips: one free submatrix per hidden state | para | change of basis | W, a generic weight matrix | Without normalization, nothing nonlinear happens between the write of  |
| 20 | Without skips: one free submatrix per hidden state | para | W_1, the chosen block | W_1, the chosen block | A symmetry can be spent. Pick $\dm$ columns of the read of $h_\ell$ th |
| 21 | Without skips: one free submatrix per hidden state | statement |  |  | \begin{restatable}[One free submatrix per hidden state]{proposition}{p |
| 22 | Without skips: one free submatrix per hidden state | para | mlp blocks only:, queries and output projections: | mlp blocks only:, queries and output projections: | Rows of a write work too: if $\dm$ rows of the write into $h_\ell$ for |
| 23 | Without skips: one free submatrix per hidden state | para |  |  | The set of functions stays the same. \Cref{sec:gain} asks what this me |
| 24 | Without skips: one free submatrix per hidden state | para |  |  | \begin{figure}[t] \centering |
| 25 | Without skips: one free submatrix per hidden state | float | U and V | U and V | \caption{(a)~A block with a learned skip is a block with $\dm$ identit |
| 26 | Learned skips are blocks of identity units | para |  |  | \subsection{Learned skips are blocks of identity units}\label{sec:lear |
| 27 | Learned skips are blocks of identity units | para |  |  | A learned skip, which adds $hA$ in place of $h$, is a block in disguis |
| 28 | Learned skips are blocks of identity units | para |  |  | \para{Merge.} Nothing nonlinear happens between $U$ and $V$, so the id |
| 29 | Learned skips are blocks of identity units | para | Lambda | Lambda | \para{Reduce.} The skip $A_\ell$ reads $h_{\ell-1}$ and writes $h_\ell |
| 30 | Learned skips are blocks of identity units | statement |  |  | \begin{restatable}[Learned skips are identity skips]{theorem}{thmLearn |
| 31 | Learned skips are blocks of identity units | para |  |  | So all $L\dm^2$ parameters of the learned skips can go, and with them  |
| 32 | Identity skips tie the hidden states | para |  |  | \subsection{Identity skips tie the hidden states}\label{sec:global}\la |
| 33 | Identity skips tie the hidden states | para |  |  | After the sweep one change of basis is left, and it must be the same a |
| 34 | Identity skips tie the hidden states | statement |  |  | \begin{restatable}[One change of basis is left]{theorem}{thmTie}\label |
| 35 | Identity skips tie the hidden states | para |  |  | So the $L$ skips remove $L\dm^2$ dimensions of symmetry. In the langua |
| 36 | Identity skips tie the hidden states | para |  |  | \para{A counterexample.} \citet[Theorem~7]{wang2025gauge} state that t |
| 37 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | \subsection{Under RMSNorm: orthogonal maps pass, triangles stay}\label |
| 38 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | With pre-RMSNorm, the network with learned skips computes \begin{equat |
| 39 | Under RMSNorm: orthogonal maps pass, triangles stay | statement |  |  | \begin{restatable}[Triangles under RMSNorm]{theorem}{thmRMSTri}\label{ |
| 40 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | \para{What a learned skip carries.} Write a skip as $A = RQ$, an upper |
| 41 | Under RMSNorm: orthogonal maps pass, triangles stay | para |  |  | LayerNorm is RMSNorm after a projection that removes the mean of each  |
| 42 | What trained models give up | para |  |  | \subsection{What trained models give up}\label{sec:trained} |
| 43 | What trained models give up | para |  |  | The reductions apply after training and keep the function. |
| 44 | What trained models give up | para |  |  | \para{A skipless ViT-B.} The skipless ViT-B of \citet{ji2026cutting} h |
| 45 | What trained models give up | para |  |  | \para{Llama-3.1.} A pre-RMSNorm language model with an untied readout  |
| 46 | Fewer parameters is not fewer functions | para |  |  | \section{Fewer parameters is not fewer functions}\label{sec:gain} \tak |
| 47 | Functional dimension | para |  |  | \subsection{Functional dimension}\label{sec:fd} |
| 48 | Functional dimension | para | F_theta, redundancy | F_theta | \para{Functional dimension.} Let $F_\theta$ be the function computed a |
| 49 | Functional dimension | para |  |  | \para{Three matrices, one map.} The linear network $x \mapsto xM_1M_2M |
| 50 | Functional dimension | statement |  |  | \begin{remark}[Large models]\label{rem:largefd} We measure small netwo |
| 51 | What the skips unlock | para |  |  | \subsection{What the skips unlock}\label{sec:count} |
| 52 | What the skips unlock | para | s, symmetries inside, script G, symmetries inside blocks | s, symmetries inside, script G, symmetries inside blocks | Blocks also have \emph{symmetries inside}, which leave the hidden stat |
| 53 | What the skips unlock | statement |  |  | \begin{restatable}[What the skips unlock]{theorem}{thmUnlock}\label{th |
| 54 | What the skips unlock | para | equality condition | equality condition | A network satisfies the \emph{equality condition} if its bound in (i)  |
| 55 | What the skips unlock | para |  |  | \para{Learned skips.} A network with learned skips has $P + L\dm^2$ pa |
| 56 | What the skips unlock | para |  |  | \para{At equal parameter count.} Under the equality condition, a resid |
| 57 | When the bounds are attained | para |  |  | \subsection{When the bounds are attained}\label{sec:onelayer} |
| 58 | When the bounds are attained | para |  |  | The equality condition is a hypothesis. We prove it in three cases. |
| 59 | When the bounds are attained | statement |  |  | \begin{restatable}[One block]{theorem}{thmOneBlock}\label{thm:oneblock |
| 60 | When the bounds are attained | statement |  |  | \begin{restatable}[Residual networks at any depth]{theorem}{thmResDept |
| 61 | When the bounds are attained | statement |  |  | \begin{restatable}[Exact gain for $\tanh$ and GELU]{theorem}{thmExactG |
| 62 | When the bounds are attained | para |  |  | \para{How the proofs go.} With one block, the parameters enter the fun |
| 63 | Measured at depth | para |  |  | \subsection{Measured at depth}\label{sec:measured} |
| 64 | Measured at depth | para |  |  | For deeper networks we compute the rank of the Jacobian on a large bat |
| 65 | Measured at depth | float |  |  | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1} \b |
| 66 | Measured at depth | para |  |  | There are two kinds of exceptions. Under RMSNorm with $\varepsilon = 1 |
| 67 | Measured at depth | statement |  |  | \begin{conjecture}[Equality condition]\label{conj:equality} Consider M |
| 68 | Measured at depth | para |  |  | For $\tanh$, GELU, SwiGLU and GeGLU blocks, the residual half of the c |
| 69 | A gap that separates function classes | para |  |  | \subsection{A gap that separates function classes}\label{sec:classes} |
| 70 | A gap that separates function classes | para |  |  | A gap in functional dimension keeps two families of functions apart. F |
| 71 | A gap that separates function classes | statement |  |  | \begin{restatable}[Different function classes]{theorem}{thmClasses}\la |
| 72 | A gap that separates function classes | para |  |  | In (ii), each extra GELU unit adds $2\dm$ parameters against a gap of  |
| 73 | Related work | para |  |  | \section{Related work}\label{sec:related} |
| 74 | Related work | para |  |  | \para{Changes of basis at hidden layers.} \citet{zhao2023symmetries} d |
| 75 | Related work | para |  |  | \para{Removing weights.} \citet{graef2024tricks} merges the queries an |
| 76 | Related work | para |  |  | \para{The basis of the residual stream.} The residual stream has no pr |
| 77 | Related work | para |  |  | \para{Symmetries and residual networks in theory.} \citet{wang2025gaug |
| 78 | Conclusion | para |  |  | \section{Conclusion}\label{sec:outlook}\label{sec:conclusion} |
| 79 | Conclusion | para |  |  | What do skips change in parameter space? They tie the bases of all hid |
| 80 | Conclusion | para |  |  | \para{Open questions.} The equality condition at depth remains open fo |
| 81 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 82 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 83 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

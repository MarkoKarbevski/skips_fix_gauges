# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para |  | RMSNorm, d_model, the model dimension, functional dimension, locally identifiable, pre-RMSNorm, redundancy | \begin{abstract} The functional dimension of a neural network is the n |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para | functional dimension |  | Which parameters of a neural network does the function that it compute |
| 3 | Introduction | para | block, d_model, the model dimension | block | We study the networks whose layers have the form of the layers of a tr |
| 4 | Introduction | para |  |  | This symmetry is known, and its use to remove parameters has barely be |
| 5 | Results | para |  |  | \subsection{Results}\label{sec:results} |
| 6 | Results | para | L, the number of blocks | L, the number of blocks, change of basis | \para{An exact reduction.} At each of the $L+1$ hidden states of a net |
| 7 | Results | para | P, the number of parameters, generic, locally identifiable, s, symmetries inside, script G, symmetries inside the blocks | P, the number of parameters, generic, s, symmetries inside, script G, symmetries inside the blocks | \para{Main result.} Whether more can be removed is a question on the f |
| 8 | Results | para |  | ReLU squared | \para{One block.} For a network of one block without normalization, we |
| 9 | Results | para |  |  | \para{What is open, and where the count fails.} At depth, the count is |
| 10 | Results | para |  |  | \para{Idea of the proof.} A direction of the parameters along which th |
| 11 | Results | float | gated block | epsilon of RMSNorm, gated block | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.1}\se |
| 12 | Related work | para |  |  | \subsection{Related work}\label{sec:related} |
| 13 | Related work | para |  |  | \Cref{sec:reduce} states what is known on the change of basis as a sym |
| 14 | Related work | para |  |  | \para{Identifiability.} The theorems of \citet{sussmann1992} and \cite |
| 15 | Related work | para |  |  | \para{Dimension counts.} \citet{grigsby2022functional} bound the funct |
| 16 | Setup | para |  |  | \section{Setup}\label{sec:setup} |
| 17 | Setup | para |  |  | This section fixes the networks. We write every block, MLP or attentio |
| 18 | Setup | para | H and d_h, ReLU squared, T, number of tokens, Wread, Wwrite, d_hidden, the number of hidden units, g, the map of a block, h, a hidden state, read / write (nouns) | H and d_h, T, number of tokens, Wread, Wwrite, d_hidden, the number of hidden units, g, the map of a block, h, a hidden state, read / write (nouns) | \para{Blocks.} A hidden state is a matrix $h \in \R^{T\times\dm}$ whos |
| 19 | Setup | para | E and D, F_theta, N(h), readout | E and D, F_theta, N(h), readout | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 20 | Setup | para | RMSNorm, epsilon of RMSNorm, pre-RMSNorm |  | \para{Normalization.} RMSNorm with the constant $\varepsilon \ge 0$ is |
| 21 | Setup | para |  |  | \para{Scope.} Networks have no biases, and their inputs range over all |
| 22 | Changes of basis, and the parameters that they remove | para |  |  | \section{Changes of basis, and the parameters that they remove}\label{ |
| 23 | Changes of basis, and the parameters that they remove | para |  |  | A symmetry is a map of the parameters that leaves the function $F_\the |
| 24 | Changes of basis, and the parameters that they remove | para | G, a change of basis | G, a change of basis | Take the first two blocks of a network without normalization. The firs |
| 25 | Changes of basis, and the parameters that they remove | statement | change of basis |  | \begin{definition}[Change of basis]\label{def:cob} The writes into the |
| 26 | Changes of basis, and the parameters that they remove | para |  |  | \para{What is known.} This section builds on results that are known, i |
| 27 | Changes of basis, and the parameters that they remove | para |  |  | \para{Pre-RMSNorm.} Under pre-RMSNorm a block reads $N_\varepsilon(h)$ |
| 28 | Changes of basis, and the parameters that they remove | statement |  |  | \begin{restatable}[Changes of basis preserve the function]{proposition |
| 29 | Changes of basis, and the parameters that they remove | para | W_1, the chosen submatrix | W_1, the chosen submatrix | \para{Removing parameters.} A change of basis that turns a $\dm\times\ |
| 30 | Changes of basis, and the parameters that they remove | statement |  |  | \begin{restatable}[Exact reduction]{proposition}{propSkipless}\label{p |
| 31 | Changes of basis, and the parameters that they remove | para |  |  | Any $\dm$ columns that form an invertible matrix serve as $W_1$, and r |
| 32 | Changes of basis, and the parameters that they remove | para |  |  | In an attention block with $Hd_h = \dm$, the matrices $W_Q$ and $W_O$  |
| 33 | Changes of basis, and the parameters that they remove | para |  |  | \para{LayerNorm and trained models.}\label{sec:trained} LayerNorm is R |
| 34 | Functional dimension and the upper bound | para |  |  | \section{Functional dimension and the upper bound}\label{sec:sym}\labe |
| 35 | Functional dimension and the upper bound | para |  |  | The reduction of \cref{sec:reduce} removes parameters without changing |
| 36 | Functional dimension and the upper bound | statement | redundancy |  | \begin{definition}[Functional dimension {\citep{grigsby2022functional} |
| 37 | Functional dimension and the upper bound | para |  |  | A continuous symmetry adds to the redundancy: if a continuous family o |
| 38 | Functional dimension and the upper bound | para |  |  | \begin{example}[Not all reductions are maximal]\label{ex:three} The li |
| 39 | Functional dimension and the upper bound | para |  |  | Two kinds of symmetry bound the functional dimension. The first are th |
| 40 | Functional dimension and the upper bound | statement |  |  | \begin{restatable}[Upper bound]{theorem}{thmUnlock}\label{thm:unlock}  |
| 41 | Functional dimension and the upper bound | para |  |  | For $\varepsilon = 0$ the same bound holds, with $\G = \CO(\dm)$, for  |
| 42 | Functional dimension and the upper bound | statement | equality condition | equality condition | \begin{definition}[Equality condition]\label{def:equality} A network s |
| 43 | Functional dimension and the upper bound | para |  |  | The reduction of \cref{prop:skipless} then leaves no redundancy but th |
| 44 | Functional dimension and the upper bound | statement | identifiable up to its symmetries | identifiable up to its symmetries | \begin{definition}[Identifiability up to symmetries]\label{def:ident}  |
| 45 | Functional dimension and the upper bound | para |  |  | The notion follows \citet{vlacic2019identifiability,vlacic2020affine}, |
| 46 | Functional dimension and the upper bound | statement |  |  | \begin{restatable}[The equality condition and local identifiability]{p |
| 47 | Functional dimension and the upper bound | para |  |  | The proposition compares only parameters that are close to each other: |
| 48 | One block | para |  |  | \section{One block}\label{sec:oneblock} |
| 49 | One block | para |  |  | The bound of \cref{thm:unlock} counts the symmetries that we know. Whe |
| 50 | One block | para | C and A of one block | C and A of one block | With one block, let $C = E\Wread$ and $A = \Wwrite D$. The network com |
| 51 | One block | para |  |  | \para{Step 1: factorizations.} The parameters enter only through $C$ a |
| 52 | One block | para |  |  | \para{Step 2: hidden units.} It remains to show that, to first order,  |
| 53 | One block | statement |  |  | \begin{restatable}[One block]{theorem}{thmOneBlock}\label{thm:oneblock |
| 54 | One block | para |  |  | Three cases of the theorem also follow from earlier work. For a $\tanh |
| 55 | Any depth | para |  |  | \section{Any depth}\label{sec:depth}\label{sec:proof} |
| 56 | Any depth | para |  |  | With several blocks, the two factorizations of \cref{sec:oneblock} are |
| 57 | Any depth | statement |  |  | \begin{restatable}[The bound is attained at any depth]{theorem}{thmSki |
| 58 | Any depth | para |  |  | Here $s = 0$ for $\tanh$ and GELU blocks, and $s$ is the number of hid |
| 59 | Any depth | para |  |  | \begin{corollary}[Local identifiability]\label{cor:skiplesslocalid} Wi |
| 60 | Any depth | para |  |  | For $\varepsilon = 0$ we state no such corollary, since \cref{prop:loc |
| 61 | One claim for every hidden state | para |  |  | \subsection{One claim for every hidden state}\label{sec:claim} |
| 62 | One claim for every hidden state | para | Lie algebra g | Lie algebra g | An MLP block acts on each token separately, so in this section inputs  |
| 63 | One claim for every hidden state | para | B_{>k} | B_{>k} | For $k = 0, \dots, L$ and a row $h$, let $\mathcal B_{>k}(h)$ be the o |
| 64 | One claim for every hidden state | para |  |  | \smallskip \noindent\emph{Claim $(D_k)$}, for $\tanh$ and GELU blocks  |
| 65 | One claim for every hidden state | para |  |  | \Cref{app:claim} states the claim in all cases: for gated blocks $\eta |
| 66 | One claim for every hidden state | para |  |  | The claim $(D_L)$ concerns the readout alone and is linear algebra (\c |
| 67 | One claim for every hidden state | para |  |  | \para{The identity for one block.} Let block $k+1$ be a $\tanh$ or GEL |
| 68 | \texorpdfstring{$\tanh$ | para |  |  | \subsection{\texorpdfstring{$\tanh$}{tanh} blocks on a ray}\label{sec: |
| 69 | \texorpdfstring{$\tanh$ | para |  |  | Take $n = t\,\xi$ with a row $\xi$, and let $t \to \infty$. With $u_j  |
| 70 | \texorpdfstring{$\tanh$ | statement |  |  | \begin{restatable}[Separation on a ray]{lemma}{lemRaySep}\label{lem:ra |
| 71 | \texorpdfstring{$\tanh$ | para |  |  | In the proof, every $\mathcal T_i$ is expanded in powers of $\zeta_1,  |
| 72 | \texorpdfstring{$\tanh$ | para |  |  | For $\sigma = \tanh$ we have $\sigma' = 1 - \sigma^2$, so the left sid |
| 73 | GELU and gated blocks on a ray | para |  |  | \subsection{GELU and gated blocks on a ray}\label{sec:raysgelu} |
| 74 | GELU and gated blocks on a ray | para |  |  | GELU and SiLU, the gate of a SwiGLU block, do not saturate. Both satis |
| 75 | GELU and gated blocks on a ray | para | frozen | frozen | The identity for one block is expanded in the products of these small  |
| 76 | GELU and gated blocks on a ray | para |  |  | \para{The later blocks.} The coefficients of the expansion come from t |
| 77 | GELU and gated blocks on a ray | para |  |  | \para{The parameters.} For $\tanh$ blocks the step holds at almost eve |
| 78 | The case \texorpdfstring{$\varepsilon = 0$ | para |  |  | \subsection{The case \texorpdfstring{$\varepsilon = 0$}{of no regulari |
| 79 | The case \texorpdfstring{$\varepsilon = 0$ | para |  |  | For $\varepsilon = 0$ the inputs of a block lie on the sphere $\norm{n |
| 80 | What is open, and where the count fails | para |  |  | \section{What is open, and where the count fails}\label{sec:open}\labe |
| 81 | What is open, and where the count fails | para |  |  | \Cref{thm:skiplessbound} leaves cases open, and for some kinds of bloc |
| 82 | What is open, and where the count fails | para |  |  | \para{Numerical ranks.} The rank of the Jacobian on a large batch of i |
| 83 | What is open, and where the count fails | statement |  |  | \begin{conjecture}[GELU blocks without normalization]\label{conj:equal |
| 84 | What is open, and where the count fails | para |  |  | \para{Attention blocks.} For attention blocks the count is proved for  |
| 85 | What is open, and where the count fails | para |  |  | \para{Where the count fails.} For ReLU, ReLU$^2$ and ReGLU blocks, the |
| 86 | Discussion | para |  |  | \section{Discussion}\label{sec:conclusion} |
| 87 | Discussion | para |  |  | A change of basis at every hidden state removes $\dm^2$ parameters fro |
| 88 | Discussion | para |  |  | \para{Skip connections.} Most networks in use add the input of a block |
| 89 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 90 | Code availability | para |  |  | \section*{Code availability} \addcontentsline{toc}{section}{Code avail |
| 91 | Code availability | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

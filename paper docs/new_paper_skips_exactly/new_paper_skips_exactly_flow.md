# Flow graph of the main text: what each unit defines and first uses

| Unit | Section | Kind | Defines | First uses | Start |
|---|---|---|---|---|---|
| 0 | abstract | para | skipless / residual network | RMSNorm, change of basis, d_model, the width, functional dimension, locally identifiable, pre-RMSNorm | \begin{abstract} It was recently shown that skip connections unlock at |
| 1 | Introduction | para |  |  | \section{Introduction}\label{sec:intro} |
| 2 | Introduction | para | d_model, the width, functional dimension, generic | generic | Skip connections are a building block of almost every deep network tra |
| 3 | Introduction | para | locally identifiable | skipless / residual network | In a network without skips, the function does not change when the outp |
| 4 | Results | para |  |  | \subsection{Results}\label{sec:results-intro} |
| 5 | Results | para | L, the number of blocks, P, the number of parameters, s, symmetries inside, script G | L, the number of blocks, P, the number of parameters, epsilon of RMSNorm, s, symmetries inside, script G | \para{Main result.} Consider a skipless network of $L$ MLP blocks of o |
| 6 | Results | para |  |  | \para{What follows.} A residual network of the same blocks has the fun |
| 7 | Results | float | d_hidden, the number of hidden units | d_hidden, the number of hidden units | \begin{table}[t] \centering\small \renewcommand{\arraystretch}{1.15}\s |
| 8 | Idea of the proof | para |  |  | \subsection{Idea of the proof}\label{sec:idea} |
| 9 | Idea of the proof | para | Wread, Wwrite | Wread, Wwrite | \para{The obstacle.} For residual networks, [KM] replace the output we |
| 10 | Idea of the proof | para |  |  | \para{Three steps.} We remove the blocks one at a time, from the first |
| 11 | Related work | para |  |  | \subsection{Related work}\label{sec:related} |
| 12 | Related work | para |  |  | \para{Identifiability.} For $\tanh$ networks, \citet{sussmann1992} and |
| 13 | Related work | para |  |  | \para{Dimension counts.} \citet{grigsby2022functional} bound the funct |
| 14 | Setup | para | g, the map of a block, q, the number of hidden units of a block | g, the map of a block, q, the number of hidden units of a block | \section{Setup}\label{sec:setup} This section fixes the networks and r |
| 15 | Setup | para | gated block, h, a hidden state, read / write (nouns) | gated block, h, a hidden state, read / write (nouns) | \para{Blocks.} A hidden state is a row $h \in \R^{1\times\dm}$: an MLP |
| 16 | Setup | para | E and D, F_theta, N(h) | E and D, F_theta, N(h) | \para{Networks.} A network has a linear embedding $E \in \R^{d_{\mathr |
| 17 | Setup | para | Lie algebra g, RMSNorm, epsilon of RMSNorm | Lie algebra g | \para{The three cases.} We write (n) for the case without normalizatio |
| 18 | Setup | para |  |  | \para{Functional dimension.} For a finite batch $X = (x_1, \dots, x_n) |
| 19 | Setup | para |  |  | \para{Symmetries.} The symmetries of a skipless network are changes of |
| 20 | Setup | para |  |  | A gated block has, in addition, one rescaling per hidden unit. For dia |
| 21 | Setup | para |  |  | Let $s = 0$ for $\tanh$ and GELU blocks and $s = q_1 + \dots + q_L$ fo |
| 22 | Setup | para | equality condition | equality condition | \para{Equality condition and local identifiability.} A network satisfi |
| 23 | Setup | para | symmetries inside blocks, symmetries inside the blocks | symmetries inside blocks, symmetries inside the blocks | \para{The residual side.} In the cases (n) and (+), the residual netwo |
| 24 | Results | para |  |  | \section{Results}\label{sec:results} |
| 25 | Results | para |  |  | \Cref{thm:skiplessbound} is the main result. \Cref{thm:epszero} gives  |
| 26 | Results | statement |  |  | \begin{restatable}[Skipless networks attain their bound]{theorem}{thmS |
| 27 | Results | para |  |  | For GELU blocks the theorem needs no more than $q_\ell \ge \dm$ hidden |
| 28 | Results | statement |  |  | \begin{restatable}[Residual networks under RMSNorm with $\varepsilon = |
| 29 | Results | para |  |  | The proof follows that of \KM{Theorem}{thm:resdepth}: with small write |
| 30 | Results | statement |  |  | \begin{restatable}[Wide GELU blocks without normalization]{proposition |
| 31 | Results | para |  |  | The proof starts from a residual network. Since GELU satisfies $\sigma |
| 32 | Results | para |  |  | \begin{corollary}[The exact gain]\label{cor:exactgain} In the cases of |
| 33 | Results | para |  |  | \begin{proof} The skipless network has the functional dimension $P - ( |
| 34 | Results | para |  |  | For one block under pre-RMSNorm, \KMp{Theorem}{thm:oneblock}{ii} gives |
| 35 | Results | para |  |  | \begin{corollary}[Skipless networks are locally identifiable]\label{co |
| 36 | Results | para |  |  | This is the equality condition together with \KM{Proposition}{prop:loc |
| 37 | Results | para |  |  | \para{Open cases.} Among the networks of \cref{tab:cases}, two cases a |
| 38 | Proof of Theorem~\ref*{thm:skiplessbound | para |  |  | \section{Proof of Theorem~\ref*{thm:skiplessbound}}\label{sec:proof} |
| 39 | Proof of Theorem~\ref*{thm:skiplessbound | para |  |  | The proof removes one block at a time. \Cref{sec:claim} reduces the th |
| 40 | One claim for every hidden state | para |  |  | \subsection{One claim for every hidden state}\label{sec:claim} |
| 41 | One claim for every hidden state | para | B_{>k} | B_{>k} | For $k = 0, \dots, L$ and a row $h$, let $\mathcal B_{>k}(h)$ be the o |
| 42 | One claim for every hidden state | para |  |  | \smallskip \noindent\emph{Claim $(D_k)$}, for $\tanh$ and GELU blocks  |
| 43 | One claim for every hidden state | para |  |  | \Cref{app:claim} states the claim in all cases: for gated blocks $\eta |
| 44 | One claim for every hidden state | para |  |  | The claim $(D_L)$ concerns the readout alone and is linear algebra (\c |
| 45 | One claim for every hidden state | para |  |  | \para{The identity for one block.} Let block $k+1$ be a $\tanh$ or GEL |
| 46 | \texorpdfstring{$\tanh$ | para |  |  | \subsection{\texorpdfstring{$\tanh$}{tanh} blocks on a ray}\label{sec: |
| 47 | \texorpdfstring{$\tanh$ | para |  |  | Take $n = t\,\xi$ with a row $\xi$, and let $t \to \infty$. With $u_j  |
| 48 | \texorpdfstring{$\tanh$ | statement |  |  | \begin{restatable}[Separation on a ray]{lemma}{lemRaySep}\label{lem:ra |
| 49 | \texorpdfstring{$\tanh$ | para |  |  | In the proof, every $\mathcal T_i$ is expanded in powers of $\zeta_1,  |
| 50 | \texorpdfstring{$\tanh$ | para |  |  | For $\sigma = \tanh$ we have $\sigma' = 1 - \sigma^2$, so the left sid |
| 51 | GELU and gated blocks on a ray | para |  |  | \subsection{GELU and gated blocks on a ray}\label{sec:raysgelu} |
| 52 | GELU and gated blocks on a ray | para |  |  | GELU and SiLU, the gate of a SwiGLU block, do not saturate. Both satis |
| 53 | GELU and gated blocks on a ray | para | frozen | frozen | The identity for one block is expanded in the products of these small  |
| 54 | GELU and gated blocks on a ray | statement |  |  | \begin{restatable}[The Mills ratio at infinity]{lemma}{lemMills}\label |
| 55 | GELU and gated blocks on a ray | para |  |  | For SwiGLU a parity argument takes the place of the lemma. The terms w |
| 56 | GELU and gated blocks on a ray | para |  |  | \para{The later blocks.} The coefficients of the expansion come from t |
| 57 | GELU and gated blocks on a ray | para |  |  | \para{The parameters.} For $\tanh$ blocks the step holds at almost eve |
| 58 | The case \texorpdfstring{$\varepsilon = 0$ | para |  |  | \subsection{The case \texorpdfstring{$\varepsilon = 0$}{of no regulari |
| 59 | The case \texorpdfstring{$\varepsilon = 0$ | para |  |  | For $\varepsilon = 0$ the inputs of a block lie on the sphere $\mathbb |
| 60 | Conclusion | para |  |  | \section{Conclusion}\label{sec:conclusion} |
| 61 | Conclusion | para |  |  | In the cases of \cref{tab:cases}, a network without skip connections h |
| 62 | Conclusion | para |  |  | \para{Open questions.} The equality condition is open for skipless net |
| 63 | Use of AI | para |  |  | \section*{Use of AI} \addcontentsline{toc}{section}{Use of AI} The con |
| 64 | Use of AI | para |  |  | \bibliographystyle{plainnat} \bibliography{refs} |

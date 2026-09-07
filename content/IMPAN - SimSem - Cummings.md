
### Radin Forcing

#### 1. Measure Sequences

Let $j:V\to M$ with $\mathrm{crit}(j) = \kappa$. Let
- $\mathcal{U}^j(0) = \kappa$;
- For all $\alpha>0$, $\mathcal{U}^j(\alpha) = \{A\subseteq V_\kappa\mid \mathcal{U}^j\upharpoonright \alpha\in j(A)\}$.
#### 2. Weak Measure Sequence

$w$ is a wms iff
- $w(0)$ is inaccessible;
- For $0<\alpha<\mathrm{lh}(w)$, $w(\alpha)$ is a measure on $V_{w(0)}$. Denote $\kappa_w = w(0)$.

$\mathcal{U}^j(\alpha)$ concentrates on wms's.

#### 3. Normality

Let $\mathcal{I}\subseteq V_\kappa$, and $(A_x)_{x\in V_\kappa}$. $A_x$ are wms's. $A_x\in \mathcal{U}^j(\alpha)$. Let
$$A = \Delta_{x\in \mathcal{I}} = \{w\in \text{wms}\cap V_\kappa\mid \forall x\in \mathcal{I}\cap V_{\kappa_w}(w\in A_x)\}.$$

*Thm.* $A\in \mathcal{U}^j(\alpha)$. *Proof.* Exercise.

*Defn.* A wms $w$ is a measure sequence if there is an elementary embedding $j$ such that $\mathrm{crit}(j) = \kappa_w$, $w = \mathcal{U}^j\upharpoonright \beta$ for some $\beta$.

"$j$ is a constructing embedding for $w$"

- $\mathcal{U}_0 = \{w\mid w\mbox{ is a measure sequence}\}$;
- $\mathcal{U}_{n+1} = \{w\in \mathcal{U}_n\mid \mbox{ Every measure on }w\mbox{ concentrates on }\mathcal{U}_n\}$;
- $\mathcal{U}_{\infty} = \bigcap_{n<\omega}\mathcal{U}_n$.
In particular: $w\in\mathcal{U}_\infty$ implies that every measure on $w$ concentrates on $\mathcal{U}_\infty$.

*Ex.* If $j:V\to \mathcal M$ and $V_{\kappa+2}\subseteq \mathcal M$, (${}^\kappa\mathcal M\subseteq\mathcal M$?), then for all $\alpha<(2^\kappa)^+$,($\mathcal U^j((2^\kappa)^+)$ exists and)  $\mathcal{U}^j\upharpoonright \alpha\in \mathcal{U}_\infty$.

*Defn.* If $w$ is a measure sequence, then $\mathcal F_w = \bigcap_{0<\alpha<\mathrm{lh}}w(\alpha)$. It is a $\kappa_w$-complete filter.

*Lem.* Let $u\in \mathcal{U}_\infty$ and $A\in\mathcal F_u$. Then 
$$B = \{w\in A\mid A\cap V_{\kappa_w}\in \mathcal F_w\}\in\mathcal F_w.$$

*Proof.* Let $j$ be constructing for $w$. The goal is to show $B\in u(\alpha)$. I.e., $u\upharpoonright\alpha\in j(B)$. $j(A)\cap V_\kappa\in \mathcal F_{u\upharpoonright\alpha}$.
- $w\in A$ and
- $A\cap V_{\kappa_w}\in \mathcal F_w$ together imply that
$w$ is addable to $(\mathcal{U}, A)$.

-------

If $\mathrm{lh}(w) = 1$, $\mathcal F_w = \{\emptyset\}$.
Given $u\in\mathcal{U}_\infty$ with $\mathrm{lh}(u)>1$, define $\Bbb R_u$ as follows:
(Intuition: Generic object will be a sequence $(w_\eta)_{\eta<\lambda}$ of measure sequences (in $\mathcal{U}_\infty\cap V_\kappa$), where $(\kappa_{w_\eta}:\eta<\lambda)$ is increasing continuous cofinal sequence in $\kappa$.)

*Defn.* Let $\vec V$ be a measure sequence. The Radin Forcing $R_{\vec{V}}$ is the set of all finite sequences $\langle d_1, \dots, d_n, \langle\kappa, \vec{V}\rangle, A\rangle$ such that: 
- 1. $A \in \bigcap \vec{V}$ and $A \subseteq \mathcal{U}_\infty$. 
- 2. $A \cap V_{\kappa(d_n)+1} = \emptyset$. 
- 3. For every $m$ with $1 \leq m \leq n$, either:
	- 3a. $d_m$ is an ordinal, or
	- 3b. $d_m = \langle \nu, \vec{F}_\nu, A_\nu \rangle$ for some $\vec{F}_\nu \in \mathcal{U}_\infty$, $A_\nu \subseteq \mathcal{U}_\infty$, and $A_\nu \in \bigcap \vec{F}_\nu$.
- 4. For every $1 \leq i < j \leq n$:
	- 4a. $\kappa(d_i) < \kappa(d_j)$, and
	- 4b. If $d_j$ is of the form $\langle \nu, \vec{F}_\nu, A_\nu \rangle$, then $A_\nu \cap V_{\kappa(d_i)+1} = \emptyset$.

*Defn.* Let $p = \langle d_1, \dots, d_n, \langle\kappa, \vec{V}\rangle, A\rangle$ and $q = \langle e_1, \dots, e_m, \langle\kappa, \vec{V}\rangle, B\rangle \in R_{\vec{V}}$. We say that $p$ is stronger than $q$ (denoted as $p \ge q$) iff: 
- 1. $A \subseteq B$. 
- 2. $n \ge m$.
- 3. There exist indices $1 \leq i_1 < i_2 < \dots < i_m \leq n$ such that for every $1 \leq k \leq m$, either:
	- 3a. $e_k = d_{i_k}$, or
	- 3b. $e_k = \langle \nu, \vec{F}_\nu, B_\nu \rangle$ and $d_{i_k} = \langle \nu, \vec{F}_\nu, C_\nu \rangle$ with $C_\nu \subseteq B_\nu$.
- 4. Using the indices $i_1, \dots, i_m$ designated in (3), the following holds for every $j$ ($1 \leq j \leq n$):
	- 4a. If $j > i_m$, then $d_j \in B$ or $d_j$ is of the form $\langle \nu, \vec{F}_\nu, C_\nu \rangle$ with $\langle \nu, \vec{F}_\nu \rangle \in B$ and $C_\nu \subseteq B \cap \nu$.
	- 4b. If $j < i_m$, let $k$ be the least integer such that $j < i_k$. Then $e_k$ is of the form $\langle \nu, \vec{F}_\nu, B_\nu \rangle$ such that:
		- i. If $d_j$ is an ordinal, then $d_j \in B_\nu$.
		- ii. If $d_j = \langle \rho, \vec{T}, S \rangle$, then $\langle \rho, \vec{T} \rangle \in B_\nu$ and $S \subseteq B_\nu$.

*Note.* $\Bbb R_\mathcal{U}$ is $\kappa^+_{\mathcal{U}}$-c.c..

*Defn.* Let $p = \langle d_1, \dots, d_n, \langle\kappa, \vec{V}\rangle, A\rangle$ and $q = \langle e_1, \dots, e_m, \langle\kappa, \vec{V}\rangle, B\rangle \in R_{\vec{V}}$. We say that $p$ is a direct (or Prikry) extension of $q$ (denoted as $p \ge^* q$) iff: 
- 1. $p \ge q$, and
- 2. $n = m$.

*Fact.* Let $p$ 

Let $(w_\eta: \eta<\lambda)$ be a generic sequence for $\Bbb R_\mathcal{U}$.
*Thm.* 
1. $\mathrm{lh}(w_\eta) = 1$ iff $\eta = 0$ or successor; $\mathrm{lh}(w_\eta) >1$ iff $\eta$ is limit.
2. For all $\eta$ limit, $\langle w_{\eta}:\eta<\lambda\rangle$ is $\Bbb R_{w_\eta}$-generic.
3. For all $A\in V$ and $A\subseteq V_{\kappa_\mathcal{U}}$, $A\in \mathcal F_\mathcal{U}$ iff $A$ contains a tail of $(w_\eta:\eta<\lambda)$. (The Magidor Condition of Radin Forcing.)

*Question.* Consider when there exists such a maximal Radin sequence of $K$.
- Mitchel et al. showed that if $o(\kappa)<\kappa$ and $\kappa$ changes cofinality, then the maximal club sets/indiscernibles always exist.
- Gitik once showed that if $o(\kappa) = \kappa$, a forcing will add lots of maximal club sets/indiscernibles but no maximal one.
- When $\mathrm{lh}(\vec V) = \kappa$, the Radin forcing make $\kappa$ to have cofinality $\omega$.
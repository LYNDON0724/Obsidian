
So far we have used the Radin forcing to *change* cofinalities: by [[Chapter 3 - The Radin Club and Changes of Cofinality#^thm-3-3-2|Theorem 3.3.2]], if $\mathrm{length}(\vec{V}) = \delta < \kappa^+$ then $\kappa$ is singularized in the extension. For applications to cardinal arithmetic one needs the opposite: force with $\mathbb{R}_{\vec{V}}$ while *keeping* $\kappa$ regular, or even measurable. A basic theme in such applications is to arrange a particular pattern of the power function over the Radin club $C_G$ (sometimes adding Cohen subsets or collapsing cardinals in between its points) and then to cut the universe at $\kappa$ — constructions of this type were used by Foreman–Woodin [12], Cummings [9] and Merimovich [40]. In this chapter we isolate the two hypotheses on $\vec{V}$ that make this possible: a **repeat point** (preserving measurability) and large cofinality of $\mathrm{length}(\vec{V})$ (preserving regularity). Throughout, $\vec{V} \in \mathcal{A}$ is a $j$-sequence with $\kappa(\vec{V}) = \kappa$, as supplied by [[Chapter 1 - Measure Sequences#^lem-1-5-1|Lemma 1.5.1]], and $G \subseteq \mathbb{R}_{\vec{V}}$ is generic.

## 4.1 Repeat points

>[!definition] Definition 4.1.1 (Gitik, Definition 5.14).
>An ordinal $\gamma < \mathrm{length}(\vec{V})$ is called a **repeat point** for $\vec{V}$ if for every $\delta$ with $\gamma \leq \delta < \mathrm{length}(\vec{V})$ and every $A \in U(\delta)$, there is a $\delta' < \gamma$ such that $A \in U(\delta')$. Equivalently, $\bigcup \vec{V} = \bigcup \vec{V} \upharpoonright \gamma$: the measures from $\gamma$ on produce no new sets.
> ^def-4-1-1

The point of the definition is that below a repeat point, the forcings $\mathbb{R}_{\vec{V}}$ and $\mathbb{R}_{\vec{V} \upharpoonright \gamma}$ are essentially the same: the conditions coincide up to replacing the top pair $\langle \kappa, \vec{V} \rangle$ by $\langle \kappa, \vec{V} \upharpoonright \gamma \rangle$, and the families of measure-one sets $\bigcap \vec{V}$ and $\bigcap \vec{V} \upharpoonright \gamma$ agree. So a generic $G \subseteq \mathbb{R}_{\vec{V}}$ may be viewed as a generic subset of $\mathbb{R}_{\vec{V} \upharpoonright \gamma}$.

>[!proposition] Proposition 4.1.2 (Gitik).
>Suppose $2^\kappa = \kappa^+$ and $\mathrm{length}(\vec{V}) = \kappa^{++}$. Then the set of repeat points for $\vec{V}$ is unbounded in $\kappa^{++}$ (indeed contains a club between $\kappa^+$ and $\kappa^{++}$). Consequently, $\vec{V} \upharpoonright \alpha$ has a repeat point for unboundedly many $\alpha < \kappa^{++}$.
> ^prop-4-1-2

*Proof.* The family $\bigcup \vec{V} = \bigcup_{\delta < \kappa^{++}} U(\delta)$ consists of subsets of $V_\kappa$, and there are only $2^\kappa = \kappa^+$ many of these. Given $\beta < \kappa^{++}$, each $A \in \bigcup_{\delta \geq \beta} U(\delta)$ appears for the first time at some stage $\delta_A$ with $\beta \leq \delta_A < \kappa^{++}$; set $\gamma = \sup\{\delta_A + 1 \mid A \in \bigcup_{\delta \geq \beta} U(\delta)\}$. Then $\gamma \geq \beta$ and $\gamma < \kappa^{++}$, since $\mathrm{cf}(\kappa^{++}) = \kappa^{++} > \kappa^+$, and by construction no measure $U(\delta)$ with $\delta \geq \gamma$ contains a set absent from all $U(\delta')$, $\delta' < \gamma$. So $\gamma$ is a repeat point above $\beta$. Applying this to the tails $\vec{V} \upharpoonright \alpha$ gives the second assertion. $\blacksquare$

## 4.2 Preserving measurability

>[!theorem] Theorem 4.2.1 (Gitik, Theorem 5.15).
>If $\gamma$ is a repeat point for $\vec{V}$ and $G \subseteq \mathbb{R}_{\vec{V}}$ is generic, then $\kappa$ remains measurable in $V[G]$.
> ^thm-4-2-1

*Proof.* Let $j : V \to M$ be a constructing embedding for $\vec{V}$, with $\mathrm{crit}(j) = \kappa$. As observed above, we may view $G$ as a generic subset of $\mathbb{R}_{\vec{V} \upharpoonright \gamma}$. Work in $V[G]$ and define, for $\dot{X}$ an $\mathbb{R}_{\vec{V}}$-name of a subset of $\kappa$:
$$\dot{X}[G] \in F \iff \text{for some } \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \in G, \text{ in } M \text{ there is } B \in \textstyle\bigcap j(\vec{V}) \text{ with}$$
$$\langle d_1, \dots, d_n, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, A \rangle, \langle j(\kappa), j(\vec{V}) \rangle, B \rangle \Vdash_{\mathbb{R}_{j(\vec{V})}} \check{\kappa} \in j(\dot{X}).$$
Thus $F$ measures $\dot{X}[G]$ by forcing "$\kappa$ enters $j(\dot{X})$" inside $M$, using a condition of $\mathbb{R}_{j(\vec{V})}$ obtained by inserting the pair $\langle \kappa, \vec{V} \upharpoonright \gamma \rangle$ with its block $A$ below the top pair $\langle j(\kappa), j(\vec{V}) \rangle$.

**$F$ is well defined.** Suppose some $\langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \in G$ forces $\dot{X} = \dot{Y}$. Then in $M$,
$$\langle d_1, \dots, d_n, \langle j(\kappa), j(\vec{V}) \rangle, j(A) \rangle \Vdash j(\dot{X}) = j(\dot{Y}).$$
Since $A \in \bigcap \vec{V}$, in particular $A \in U(\gamma)$, so $\langle \kappa, \vec{V} \upharpoonright \gamma \rangle \in j(A)$ by the definition of the $j$-sequence; also $j(A) \cap V_\kappa = A$. Hence the triple $\langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, A \rangle$ is addible to this condition, and for every $B \in \bigcap j(\vec{V})$,
$$\langle d_1, \dots, d_n, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, A \rangle, \langle j(\kappa), j(\vec{V}) \rangle, B \cap j(A) \rangle \Vdash \check{\kappa} \in j(\dot{X}) \wedge j(\dot{X}) = j(\dot{Y}),$$
so the definition of $F$ does not depend on the choice of the name or of the condition in $G$.

>[!exercise] Exercise 4.2.2.
>Show that $F$ is a $\kappa$-complete ultrafilter on $\kappa$ extending $U(0)$. (Hint: ultrafilterness uses genericity — some condition in $G$ decides $\dot{X}$ — together with the well-definedness computation; $\kappa$-completeness uses that the relevant filters are $\kappa$-complete and that direct extensions decide bounded meets.)
> ^ex-4-2-2

**Normality of $F$.** Suppose $\langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \in G$ forces "$\{\nu < \kappa \mid \dot{f}(\nu) < \nu\} \in \dot{F}$". Then in $M$, for some $B \in \bigcap j(\vec{V})$,
$$\langle d_1, \dots, d_n, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, A \rangle, \langle j(\kappa), j(\vec{V}) \rangle, B \rangle \Vdash j(\dot{f})(\check{\kappa}) < \check{\kappa}.$$
Working in $M$, construct $B' \in \bigcap j(\vec{V})$ by a diagonal intersection (in the sense of [[Chapter 1 - Measure Sequences#^def-1-3-1|Definition 1.3.1]]) over the $\kappa$ many relevant lower parts, so that: whenever for some $\nu < \kappa$ a condition $\langle x_1, \dots, x_\ell, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, C \rangle, \langle j(\kappa), j(\vec{V}) \rangle, E \rangle$ forces $j(\dot{f})(\check{\kappa}) = \check{\nu}$, then the same condition with $E$ replaced by $B'$ forces it as well.

Back in $V$, let
$$D = \left\{ \langle x_1, \dots, x_\ell, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, C \rangle \rangle \in \mathbb{R}_{\vec{V} \upharpoonright \gamma} \,\middle|\, \text{for some } \nu < \kappa,\ \langle x_1, \dots, x_\ell, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, C \rangle, \langle j(\kappa), j(\vec{V}) \rangle, B' \rangle \Vdash j(\dot{f})(\check{\kappa}) = \check{\nu} \right\}.$$
We claim $D$ is dense in $\mathbb{R}_{\vec{V} \upharpoonright \gamma}$ below $\langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$. Given any stronger condition $p$, the condition $p^\frown \langle \langle j(\kappa), j(\vec{V}) \rangle, B' \rangle$ of $\mathbb{R}_{j(\vec{V})}$ (computed in $M$) is stronger than the displayed condition above, hence forces $j(\dot{f})(\check{\kappa}) < \check{\kappa}$; some stronger condition $\langle x_1, \dots, x_\ell, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, C \rangle, \langle j(\kappa), j(\vec{V}) \rangle, E \rangle$ decides the value, say $\check{\nu}$. By the uniform property of $B'$, replacing $E$ by $B'$ still decides $\check{\nu}$, so $\langle x_1, \dots, x_\ell, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, C \rangle \rangle \in D$ and is stronger than $p$.

Pick $\langle e_1, \dots, e_m, \langle \kappa, \vec{V} \rangle, A' \rangle \in G \cap D$ below $\langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$. There is $\delta < \kappa$ such that
$$\langle e_1, \dots, e_m, \langle \langle \kappa, \vec{V} \upharpoonright \gamma \rangle, A' \rangle, \langle j(\kappa), j(\vec{V}) \rangle, B' \rangle \Vdash j(\dot{f})(\check{\kappa}) = \check{\delta},$$
and then $\{\nu < \kappa \mid \dot{f}(\nu) = \delta\} \in F$ by the definition of $F$. Hence $F$ is normal, and $\kappa$ is measurable in $V[G]$. $\blacksquare$

*Remark (Gitik).* The ultrafilter $F$ defined above extends $U(0)$, but its ultrapower embedding does not extend that of $U(0)$; instead it extends a certain iterated ultrapower embedding using ultrafilters of $\mathrm{Ult}(V, U(0))$ between $\kappa$ and $i_{U(0)}(\kappa)$. Similar arguments show that the degree of *strongness*, and even of *supercompactness*, of the embedding $j$ can be preserved. Note the contrast with Chapter 3: preserving measurability costs a repeat point, which by [[Chapter 1 - Measure Sequences#^lem-1-5-1|Lemma 1.5.1]] and Proposition 4.1.2 requires a long sequence ($\mathrm{length}(\vec{V}) = \kappa^{++}$ under $2^\kappa = \kappa^+$), while changing the cofinality of $\kappa$ to $\aleph_0$ already works at length $2$.

## 4.3 Fat trees

For regularity we need a strengthening of the Prikry property ([[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]]) in the spirit of the tree formulation of Prikry forcing: to land in a dense open set, one should only have to specify *which* measures are used and measure-one sets in them — not *which* points are picked.

>[!definition] Definition 4.3.1 (Gitik, Definition 5.16).
>Let $\vec{F}$ be a sequence of ultrafilters over $V_\nu$ for some $\nu \leq \kappa$. A tree $T \subseteq [V_\nu]^{\leq n}$ with $n < \omega$ levels is called **$\vec{F}$-fat** iff
>(1) for every $\langle \nu_1, \dots, \nu_k \rangle \in T$, $\kappa(\nu_1) < \kappa(\nu_2) < \dots < \kappa(\nu_k)$;
>(2) for every non-maximal $\langle \nu_1, \dots, \nu_k \rangle \in T$ ($k < n$), there is an $\alpha < \mathrm{length}(\vec{F})$ such that $\mathrm{Suc}_T(\langle \nu_1, \dots, \nu_k \rangle) \in F(\alpha)$.
> ^def-4-3-1

>[!definition] Definition 4.3.2 (Gitik).
>Let $T$ be $\vec{F}$-fat and let $\eta = \langle \eta(1), \dots, \eta(n) \rangle$ be a maximal branch of $T$. A sequence $\vec{A} = \langle \vec{A}(1), \dots, \vec{A}(n) \rangle \in [V_\nu]^n$ is called a sequence of **$\eta$-measure one** if for every $i$ with $\eta(i)$ of the form $\langle \tau_i, \vec{G}_{\tau_i} \rangle$ we have $\vec{A}(i) \in \bigcap \vec{G}_{\tau_i}$.
>
>Let $p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \in \mathbb{R}_{\vec{V}}$, and write $\langle \langle \nu_{n+1}, \vec{F}_{n+1} \rangle, A_{n+1} \rangle$ for the top pair $\langle \langle \kappa, \vec{V} \rangle, A \rangle$. Let $1 \leq i_1 < \dots < i_m \leq n+1$ be indices with $d_{i_k} = \langle \langle \nu_{i_k}, \vec{F}_{i_k} \rangle, A_{i_k} \rangle$, and for each $k$ let $T_k \subseteq [V_{\nu_{i_k}}]^{n_k}$ be an $\vec{F}_{i_k}$-fat tree, $\eta_k$ a maximal branch of $T_k$, and $\vec{A}_k$ a sequence of $\eta_k$-measure one. We denote by
>$$p^\frown \langle \eta_1, \vec{A}_1 \rangle^\frown \cdots^\frown \langle \eta_m, \vec{A}_m \rangle$$
>the condition obtained from $p$ by inserting, for each $k$, the sequence $\eta_k$ between $d_{i_k - 1}$ and $d_{i_k}$ — an ordinal point $\eta_k(j)$ is inserted as an ordinal, a pair $\eta_k(j) = \langle \tau_j, \vec{G}_{\tau_j} \rangle$ as the triple $\langle \tau_j, \vec{G}_{\tau_j}, \vec{A}_k(j) \rangle$ — and then shrinking all blocks in the unique minimal way required by [[Chapter 2 - The Radin Forcing#^def-2-2-1|Definition 2.2.1]] (each block is cut down to avoid $V_{\kappa(t)+1}$ for the preceding entry $t$).
> ^def-4-3-2

>[!lemma] Lemma 4.3.3 (Gitik, Lemma 5.17).
>Let $D$ be a dense open subset of $\mathbb{R}_{\vec{V}}$ and $p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \in \mathbb{R}_{\vec{V}}$. Then there are $p^* = \langle d_1^*, \dots, d_n^*, \langle \kappa, \vec{V} \rangle, A^* \rangle \leq^* p$; indices $1 \leq i_1 < \dots < i_m \leq n+1$; and for $1 \leq k \leq m$, $\vec{F}_{i_k}$-fat trees $T_k \subseteq [V_{\nu_{i_k}}]^{n_k}$, such that:
>for every sequence $\langle \eta_k \mid 1 \leq k \leq m \rangle$ with $\eta_k$ a maximal branch of $T_k$, there are sequences $\vec{A}_k$ of $\eta_k$-measure one with
>$$p^* {}^\frown \langle \eta_1, \vec{A}_1 \rangle^\frown \cdots^\frown \langle \eta_m, \vec{A}_m \rangle \in D.$$
> ^lem-4-3-3

*Remark (Gitik, Remark 5.18).* Roughly, the meaning is this: in order to get into $D$ we need to specify certain ultrafilters $U(\alpha)$ (or $F(\alpha)$, below $\kappa$) and measure-one sets in them; then *any* choice of points from these sets puts us into $D$.

*Proof.* The proof is a refinement of that of [[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]], and we use the notation set up there ($\tilde{A}(\vec{d})$, $A(\alpha, \vec{d})$, $A(\alpha)$, diagonal intersections). We treat the case $p = \langle \langle \kappa, \vec{V} \rangle, A \rangle$; the general case is obtained by applying the same argument inside the block of each triple of the stem, as in the reduction in Lemma 2.4.4. So we need $p^* = \langle \langle \kappa, \vec{V} \rangle, A^* \rangle \leq^* p$ and a $\vec{V}$-fat tree $T$ of some finite height such that for every maximal branch $\eta$ of $T$ there is a sequence $\vec{A}$ of $\eta$-measure one with $p^* {}^\frown \langle \eta, \vec{A} \rangle \in D$.

If $p$ already has a direct extension in $D$, take such an extension and $T = \{\langle \rangle\}$. Assume this is not the case. For each finite sequence $\vec{d}$ with $\vec{d}^\frown p \in \mathbb{R}_{\vec{V}}$, split $\tilde{A}(\vec{d})$ into two parts according to whether a one-step extension $\vec{d}^\frown d^\frown p$ has a direct extension in $D$:
$$A_0(\vec{d}) = \{d \in \tilde{A}(\vec{d}) \mid \vec{d}^\frown d^\frown p \text{ has a direct extension in } D\}, \qquad A_1(\vec{d}) = \tilde{A}(\vec{d}) \setminus A_0(\vec{d});$$
for $d = \langle \nu, \vec{F}_\nu \rangle$ "direct extension" includes the freedom to shrink the block of the new triple, i.e. $\vec{d}^\frown \langle \nu, \vec{F}_\nu, b_d \rangle^\frown \langle \langle \kappa, \vec{V} \rangle, B_d \rangle \in D$ for some $b_d \in \bigcap \vec{F}_\nu$ and $B_d \in \bigcap \vec{V}$. For each $\alpha < \mathrm{length}(\vec{V})$ choose the side $i_\alpha \leq 1$ with $A_{i_\alpha}(\vec{d}) \in U(\alpha)$, set $A(\alpha, \vec{d}) = A_{i_\alpha}(\vec{d})$, and let $A(\alpha)$ be the diagonal intersection; set $A_1 = \bigcup\{A(\alpha) \mid \alpha < \mathrm{length}(\vec{V})\}$ and $p_1 = \langle \langle \kappa, \vec{V} \rangle, A_1 \rangle$. As in Lemma 2.4.4 we get:
$$(\star)_1 \quad \text{if } p_1 \leq q = \langle e_0, \dots, e_m, \langle \kappa, \vec{V} \rangle, B \rangle \in D, \text{ then there is } \alpha < \mathrm{length}(\vec{V}) \text{ such that for every } e'_m \in A(\alpha) \setminus V_{\kappa(e_{m-1})+1}, \ \langle e_0, \dots, e_{m-1}, e'_m, \langle \kappa, \vec{V} \rangle, A_1 \rangle \text{ has a direct extension in } D.$$

If now for some $d \in A_1$ the condition $d^\frown p_1$ has a direct extension in $D$, we finish at height $1$: fix $\alpha$ with $d \in A(\alpha)$, for each $d' \in A(\alpha)$ fix a direct extension $\langle \tilde{d}', \langle \kappa, \vec{V} \rangle, B_{d'} \rangle \in D$ of $d'^\frown p_1$ (where $\tilde{d}' = d'$ for ordinals and $\tilde{d}' = \langle \nu, \vec{F}_\nu, b_{d'} \rangle$ for pairs), and let $A^*$ be the diagonal intersection $\{e \in A_1 \mid \forall d' \in V_{\kappa(e)}\ (e \in B_{d'})\} \in \bigcap \vec{V}$; then $A^* \setminus V_{\kappa(d')+1} \subseteq B_{d'}$ for each $d'$, so by openness $\langle \tilde{d}', \langle \kappa, \vec{V} \rangle, A^* \setminus V_{\kappa(d')+1} \rangle \in D$ for all $d' \in A(\alpha) \cap A^*$, and we take $p^* = \langle \langle \kappa, \vec{V} \rangle, A^* \rangle$ with $T$ the one-level tree whose level is $A(\alpha) \cap A^*$.

Otherwise we pass to two-step extensions: replacing $A$ by $A_1$, define $\tilde{A}(\vec{d})$ as above and let $A_0(\vec{d})$ consist of those $d$ for which there are $\alpha(\vec{d}) < \mathrm{length}(\vec{V})$ and a set $C(\vec{d}) \subseteq \tilde{A}(\vec{d}) \setminus V_{\kappa(d)+1}$, $C(\vec{d}) \in U(\alpha(\vec{d}))$, such that for every $c \in C(\vec{d})$ the condition $\vec{d}^\frown d^\frown c^\frown p_1$ has a direct extension in $D$. Define the $A(\alpha, \vec{d})$'s, $A(\alpha)$'s, $A_2$ and $p_2$ as before. If for some $d_1, d_2 \in A_2$ a direct extension of ${d_1}^\frown {d_2}^\frown p_2$ is in $D$, then by $(\star)_1$ there is $\beta < \mathrm{length}(\vec{V})$ such that for *every* $d'_2 \in A_1(\beta) \setminus V_{\kappa(d_1)+1}$ the condition ${d_1}^\frown {d'_2}^\frown p_2$ has a direct extension in $D$; and then for $\alpha$ with $d_1 \in A(\alpha)$ we have $d_1 \in A_0(\langle \rangle)$, so every $d'_1 \in A(\alpha)$ has the same property for some $\beta'$. We finish with a two-level tree, as above.

Continue in the same fashion. At stage $n$ we have sets $A_n(\alpha) \in U(\alpha)$, $A_n = \bigcup_\alpha A_n(\alpha)$, $p_n = \langle \langle \kappa, \vec{V} \rangle, A_n \rangle$, and the $n$-dimensional version of $(\star)_1$:
$$(\star)_n \quad \text{if } p_n \leq q = \langle e_0, \dots, e_{m-1}, d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, B \rangle \in D, \text{ then there is an } n\text{-level } \vec{V}\text{-fat tree } T_q \text{ such that for every maximal branch } \eta \text{ of } T_q \text{ there are a sequence } \vec{A} \text{ of } \eta\text{-measure one and } B_\eta \in \textstyle\bigcap \vec{V} \text{ with } \langle e_0, \dots, e_{m-1} \rangle^\frown \langle \eta, \vec{A} \rangle^\frown \langle \langle \kappa, \vec{V} \rangle, B_\eta \rangle \in D.$$
If for some $d_1, \dots, d_n \in A_n$ a direct extension $q$ of $\langle d_1, \dots, d_n \rangle^\frown p_n$ is in $D$, we finish: take $T = T_q$ from $(\star)_n$ and let $A^* = \{e \in A_n \mid \forall \eta \in V_{\kappa(e)}\ (e \in B_\eta)\}$ (the diagonal intersection of the $B_\eta$'s), so that $p^* = \langle \langle \kappa, \vec{V} \rangle, A^* \rangle$ works by openness of $D$.

Suppose, towards a contradiction, that the process does not stop at any $n < \omega$. Set
$$p^* = \Bigl\langle \langle \kappa, \vec{V} \rangle, \bigcap_{n < \omega} A_n \Bigr\rangle;$$
then $p^* \leq^* p$ (the intersection is in $\bigcap \vec{V}$ by $\kappa$-completeness), and by our assumption no direct extension of $p^*$ lies in $D$. Pick $q = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, B \rangle \leq p^*$ with $q \in D$. Then $q \leq^* \langle d_1, \dots, d_n \rangle^\frown p_n$, since the stem entries of $q$ lie in $A^* \subseteq A_n$. But by the construction at stage $n$, the existence of such a $q$ means the process was supposed to stop at stage $n$. Contradiction. $\blacksquare$

## 4.4 Preserving regularity

>[!theorem] Theorem 4.4.1 (Gitik, Theorem 5.19).
>If $\mathrm{cf}(\mathrm{length}(\vec{V})) \geq \kappa^+$, then $\kappa$ remains regular (and hence inaccessible) in $V^{\mathbb{R}_{\vec{V}}}$.
> ^thm-4-4-1

*Proof.* Cardinals are preserved by [[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]], and $\kappa$ is a strong limit in $V$, so it is enough to show that $\kappa$ is not singularized. Suppose $\delta < \kappa$ and $\dot{f}$ is an $\mathbb{R}_{\vec{V}}$-name such that the weakest condition forces $\dot{f} : \check{\delta} \to \check{\kappa}$. Let $t = \langle \mu_1, \dots, \mu_s, \langle \kappa, \vec{V} \rangle, E \rangle \in \mathbb{R}_{\vec{V}}$; we find a $p \leq t$ forcing "$\mathrm{ran}\, \dot{f}$ is bounded in $\check{\kappa}$". For $\xi < \delta$ consider
$$D_\xi = \{p \in \mathbb{R}_{\vec{V}} \mid \text{for some } d \in V_\kappa \setminus V_{\mu_s + 1} \text{ appearing in } p,\ p \Vdash \dot{f}(\check{\xi}) < \check{\kappa}(d)\}.$$
Clearly $D_\xi$ is dense (decide the value of $\dot{f}(\check{\xi})$ and append an ordinal above it).

For every $\vec{d} = \langle d_1, \dots, d_n \rangle \in V_\kappa$ with $\vec{d}^\frown \langle \langle \kappa, \vec{V} \rangle, V_\kappa \setminus V_{\kappa(d_n)+1} \rangle \in \mathbb{R}_{\vec{V}}$, apply Lemma 4.3.3 to this condition and $D_\xi$; we are interested only in the last tree $T_m$, and only when $i_m = n+1$, i.e. the tree hanging at the top pair. This $T_m$ is a $\vec{V}$-fat tree of some finite height; denote it by $T(\xi, \vec{d})$. For every non-maximal node $\eta$ of $T(\xi, \vec{d})$ there is $\alpha(\eta) < \mathrm{length}(\vec{V})$ with $\mathrm{Suc}(\eta) \in U(\alpha(\eta))$; set
$$\alpha(\vec{d}) = \textstyle\bigcup\{\alpha(\eta) \mid \eta \in T(\xi, \vec{d}) \text{ non-maximal}\}.$$
Since $T(\xi, \vec{d}) \subseteq V_\kappa$ has at most $\kappa$ many nodes and $\mathrm{cf}(\mathrm{length}(\vec{V})) \geq \kappa^+$, we have $\alpha(\vec{d}) < \mathrm{length}(\vec{V})$. Then $\alpha(\xi) = \bigcup\{\alpha(\vec{d}) \mid \vec{d} \in V_\kappa\} < \mathrm{length}(\vec{V})$ (there are $\kappa$ many $\vec{d}$'s), and finally pick $\alpha < \mathrm{length}(\vec{V})$ above every $\alpha(\xi)$, $\xi < \delta$. Consider
$$B = \{\langle \nu, \vec{F}_\nu \rangle \in V_\kappa \mid \forall \xi < \delta\ \forall \vec{d} \in V_\nu\ (T(\xi, \vec{d}) \cap V_\nu \text{ is } \vec{F}_\nu\text{-fat})\}.$$
Then $B \in U(\alpha)$: in $M$, at the pair $\langle \kappa, \vec{V} \upharpoonright \alpha \rangle$, the condition reads "$j(T)(\xi, \vec{d}) \cap V_\kappa$ is $(\vec{V} \upharpoonright \alpha)$-fat" for all $\xi < \delta$ and $\vec{d} \in V_\kappa$; but $j$ fixes $V_\kappa$ pointwise, so $j(T)(\xi, \vec{d}) \cap V_\kappa = T(\xi, \vec{d})$, and $T(\xi, \vec{d})$ is $\vec{V}$-fat with successor measures taken from $\{U(\beta) \mid \beta < \alpha(\xi)\}$, all of which lie in $\vec{V} \upharpoonright \alpha$ since $\alpha(\xi) < \alpha$.

For every $\xi < \delta$, let $A_\xi^* \in \bigcap \vec{V}$ be the set given by Lemma 4.3.3 applied to $D_\xi$ and $t$, and let $A^* = \bigcap_{\xi < \delta} A_\xi^* \in \bigcap \vec{V}$.

**Claim.** Let $p \leq \langle \mu_1, \dots, \mu_s, \langle \kappa, \vec{V} \rangle, A^* \setminus V_{\mu_s + 1} \rangle$ and suppose some $\langle \nu, \vec{F}_\nu \rangle \in B \setminus V_{\mu_s + 1}$ appears in $p$. Then $p \Vdash \forall \xi < \check{\delta}\ (\dot{f}(\xi) < \check{\nu})$.

*Proof of Claim.* Suppose not: let $p$ be as above with $p \Vdash \dot{f}(\check{\xi}) \geq \check{\nu}$ for some $\xi < \delta$, and write
$$p = \langle d_1, \dots, d_\ell, \langle \langle \nu, \vec{F}_\nu \rangle, a_\nu \rangle, d_{\ell+2}, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle.$$
Set $p' = \langle d_1, \dots, d_\ell, \langle \kappa, \vec{V} \rangle, A^* \setminus V_{\kappa(d_\ell)+1} \rangle$. By the definition of $B$, the tree $T(\xi, \langle d_1, \dots, d_\ell \rangle) \cap V_\nu$ is $\vec{F}_\nu$-fat. Since $a_\nu \in \bigcap \vec{F}_\nu$, we can choose, level by level, a maximal branch $\langle f_1, \dots, f_m \rangle$ through this tree lying inside $a_\nu$: at each non-maximal node the successor set lies in some $F_\nu(\beta)$ and hence meets $a_\nu$. By Lemma 4.3.3 and the remark following it, there is $q \leq p'$ with $q \in D_\xi$ of the form
$$q = \langle e_1, \dots, e_i, \tilde{f}_1, \dots, \tilde{f}_m, \langle \kappa, \vec{V} \rangle, A^* \setminus V_{\kappa(f_m)+1} \rangle,$$
where $\kappa(e_i) = \kappa(d_\ell)$ and each $\tilde{f}_j$ is $f_j$ (for ordinals) or $\langle f_j, b_j \rangle$ for some $b_j$ (for pairs). Since $q \in D_\xi$, $q \Vdash \dot{f}(\check{\xi}) < \check{\kappa}(f_m)$, and $\kappa(f_m) < \nu$ because $f_m \in a_\nu \subseteq V_\nu$.

On the other hand $q$ and $p$ are compatible: $p \leq \langle \mu_1, \dots, \mu_s, \langle \kappa, \vec{V} \rangle, A^* \setminus V_{\mu_s+1} \rangle$, so the entries $\langle \langle \nu, \vec{F}_\nu \rangle, a_\nu \rangle, d_{\ell+2}, \dots, d_n$ of $p$ come from $A^*$ and are addible to $q$ above $f_m$; hence
$$\langle e_1, \dots, e_i, \tilde{f}_1, \dots, \tilde{f}_m, \langle \langle \nu, \vec{F}_\nu \rangle, a_\nu \setminus V_{\kappa(f_m)+1} \rangle, d_{\ell+2}, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$$
is a common extension. But it must force both $\dot{f}(\check{\xi}) < \check{\nu}$ (via $q$) and $\dot{f}(\check{\xi}) \geq \check{\nu}$ (via $p$). Contradiction. $\blacksquare$

Finally, every condition below $t$ can be extended to one as in the Claim: shrink the measure-one sets into $A^*$ and append a pair from $B \setminus V_{\mu_s+1}$ (possible since $B \in U(\alpha)$ and every set in $\bigcap \vec{V}$ meets $B$). Hence the conditions forcing "$\mathrm{ran}\, \dot{f}$ is bounded in $\check{\kappa}$" are dense below $t$, and since $t$ was arbitrary, the weakest condition forces that $\dot{f}$ is not cofinal in $\kappa$. $\blacksquare$

>[!corollary] Corollary 4.4.2 (Gitik, Remark 5.20).
>The converse of Theorem 4.4.1 fails: by Theorem 4.2.1, if $\vec{V}$ has a repeat point $\gamma$ then $\kappa$ remains measurable — hence regular — in $V[G]$, while e.g. a sequence of length $\gamma + 1$ may have $\mathrm{cf}(\mathrm{length}(\vec{V})) = \aleph_0 < \kappa^+$.
> ^cor-4-4-2

>[!exercise] Exercise 4.4.3.
>Let $\mathrm{cf}(\mathrm{length}(\vec{V})) \geq \kappa^+$ and $G \subseteq \mathbb{R}_{\vec{V}}$ generic. Determine the order type of the Radin club $C_G$ in $V[G]$. (Hint: combine [[Chapter 3 - The Radin Club and Changes of Cofinality#^lem-3-1-2|Lemma 3.1.2]] with Theorem 4.4.1 — a club in a *regular* $\kappa$ must have order type $\kappa$; contrast with [[Chapter 3 - The Radin Club and Changes of Cofinality#^thm-3-3-2|Theorem 3.3.2]].)
> ^ex-4-4-3

---

## Notes

Definition 4.1.1, Theorem 4.2.1, Definition 4.3.1, Lemma 4.3.3 and Theorem 4.4.1 are Gitik's Definition 5.14, Theorem 5.15, Definition 5.16, Lemma 5.17 and Theorem 5.19, respectively; Corollary 4.4.2 is his Remark 5.20, and the remark after Lemma 4.3.3 is his Remark 5.18. In Theorem 4.2.1 we have used factorization ([[Chapter 2 - The Radin Forcing#^lem-2-4-2|Lemma 2.4.2]]) where Gitik phrases the density argument in terms of the forcing $\mathbb{R}_{j(\vec{V})} \setminus \kappa + 1$; the content is the same. The observation that regularity preservation is the key to applications in cardinal arithmetic — arranging a pattern of the power function along $C_G$ and cutting the universe at $\kappa$ — is Gitik's, with references to Foreman–Woodin [12], Cummings [9] and Merimovich [40]. In Chapter 5 we will see that all of these results have cheaper analogues: coherent sequences of measures allow the same conclusions from Mitchell-order hypotheses alone.

## References

Main reference:

- Moti Gitik. Prikry-type forcings. In Matthew Foreman and Akihiro Kanamori, editors, *Handbook of Set Theory*, pages 1351–1447. Springer, Dordrecht, 2010.

Numbering below follows the bibliography of Gitik's chapter:

- [ ] James Cummings. A model in which GCH holds at successors but fails at limits. *Transactions of the American Mathematical Society*, 329(1):1–39, 1992.
- [12] Matthew Foreman and W. Hugh Woodin. The generalized continuum hypothesis can fail everywhere. *Annals of Mathematics (2)*, 133(1):1–35, 1991.
- [40] Carmi Merimovich. A power function with a fixed finite gap everywhere. *The Journal of Symbolic Logic*, 72:361–417, 2007.

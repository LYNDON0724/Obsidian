
The forcing $\mathbb{R}_{\vec{V}}$ of Chapter 2 is defined from a $j$-sequence of ultrafilters, and producing long such sequences costs serious large cardinal strength ([[Chapter 1 - Measure Sequences#^lem-1-5-1|Lemma 1.5.1]]): already length $2$ needs a μ-measurable cardinal. It was Mitchell's insight [42] that the *embedding is not really needed*: all the combinatorics of the forcing only ever uses the sequence of measures together with a **coherence** property, and coherent sequences exist already at the level of Mitchell order. This lowers the hypotheses to optimal ones and yields equiconsistency results; it also gives a uniform treatment of Magidor's forcing [37], which we take up in Chapter 6. In this chapter we define coherent sequences, build the forcing $\mathbb{P}_{\vec{U}}$ on them, and explain why every theorem of Chapters 2–4 transfers to it.

## 5.1 Coherent sequences of measures

>[!definition] Definition 5.1.1 (Gitik, Definition 5.21; Mitchell [43]).
>A **coherent sequence of measures** is a function $\vec{U}$ with domain of the form
>$$\mathrm{dom}(\vec{U}) = \{(\alpha, \beta) \mid \alpha < \ell^{\vec{U}},\ \beta < o^{\vec{U}}(\alpha)\}$$
>for an ordinal $\ell^{\vec{U}}$ (the **length** of $\vec{U}$) and a function $o^{\vec{U}}$ (the **order** of $\vec{U}$), such that for every $(\alpha, \beta) \in \mathrm{dom}(\vec{U})$:
>(1) $U(\alpha, \beta)$ is a normal ultrafilter over $\alpha$;
>(2) (**coherence**) if $j^\alpha_\beta : V \to N^\alpha_\beta \simeq \mathrm{Ult}(V, U(\alpha, \beta))$ is the ultrapower embedding, then
>$$j^\alpha_\beta(\vec{U}) \upharpoonright \alpha + 1 = \vec{U} \upharpoonright (\alpha, \beta),$$
>where $\vec{U} \upharpoonright \alpha = \vec{U} \upharpoonright \{(\alpha', \beta') \mid \alpha' < \alpha,\ \beta' < o^{\vec{U}}(\alpha')\}$ and $\vec{U} \upharpoonright (\alpha, \beta) = \vec{U} \upharpoonright \{(\alpha', \beta') \mid (\alpha' < \alpha \text{ and } \beta' < o^{\vec{U}}(\alpha')) \text{ or } (\alpha' = \alpha \text{ and } \beta' < \beta)\}$.
> ^def-5-1-1

So $\vec{U}$ is a sequence of normal measures organized by Mitchell order, and coherence says that each measure knows exactly the part of the sequence below it: in the ultrapower by $U(\alpha, \beta)$, the sequence up to $\alpha$ is $\vec{U}$ itself, and the measures on $\alpha$ are precisely $U(\alpha, \beta')$ for $\beta' < \beta$. In particular $o^{\vec{U}}(\alpha)$ is the Mitchell order of $\alpha$ as computed with the measures of $\vec{U}$, and the existence of a coherent sequence with $o^{\vec{U}}(\kappa) = \delta$ follows from $o(\kappa) \geq \delta$ — no extenders needed.

**Convention.** Note that the measures $U(\alpha, \beta)$ are ultrafilters over the *ordinal* $\alpha$, not over $V_\alpha$; this is the classical setting of the Mitchell order, and it is what makes Magidor forcing fall out directly in Chapter 6. (Via a coding of $\alpha$ by $V_\alpha$ the two presentations are interchangeable; cf. the convention of Chapter 2.)

**Replacing $\vec{V}$ by $\vec{U}$.** Suppose now that $\ell^{\vec{U}} = \kappa + 1$ and $o^{\vec{U}}(\kappa) = \delta > 0$. Over $\kappa$ we use the sequence
$$\vec{U}(\kappa) = \langle U(\kappa, \alpha) \mid \alpha < \delta \rangle$$
in the role that $\vec{V}$ played in Chapters 1–4. A set $A \in \bigcap \vec{U}(\kappa)$ consists of ordinals only — there are no more pairs $\langle \nu, \vec{F}_\nu \rangle$ carried inside measure-one sets. But whenever $\nu \in A$ has $o^{\vec{U}}(\nu) > 0$, the sequence
$$\vec{U}(\nu) = \langle U(\nu, \alpha) \mid \alpha < o^{\vec{U}}(\nu) \rangle$$
is available and can play the role of $\vec{F}_\nu$; it is determined uniquely by $\nu$ and $\vec{U}$, which is why the conditions of the forcing below need not carry the measure sequences around.

This is where Chapter 1 becomes dispensable: the hierarchy $\mathcal{A}$ of [[Chapter 1 - Measure Sequences#^def-1-4-2|Definition 1.4.2]] was needed because a pair $\langle \nu, \vec{F}_\nu \rangle$ drawn from a measure-one set had to be *certified* as itself coming from an embedding (so that the recursion could continue below $\nu$); here coherence certifies every $\vec{U}(\nu)$ at once, as the following lemma shows.

>[!lemma] Lemma 5.1.2 (Coherence implies addability).
>Let $\vec{U}$ be coherent, $\beta < \alpha < \kappa$ and $A \in U(\kappa, \alpha) \cap U(\kappa, \beta)$. Then
>$$\{\nu < \kappa \mid o^{\vec{U}}(\nu) > \beta \text{ and } A \cap \nu \in U(\nu, \beta)\} \in U(\kappa, \alpha).$$
> ^lem-5-1-2

*Proof.* Let $j = j^\kappa_\alpha : V \to M$. By coherence, the $\beta$-th measure on $\kappa$ in $j(\vec{U})$ is $U(\kappa, \beta)$ itself; in particular $U(\kappa, \beta) \in M$. By Łoś, the displayed set lies in $U(\kappa, \alpha)$ iff in $M$, $j(A) \cap \kappa$ belongs to the $\beta$-th measure on $\kappa$ of $j(\vec{U})$, i.e. iff $j(A) \cap \kappa \in U(\kappa, \beta)$. But $j(A) \cap \kappa = A$ (since $\mathrm{crit}(j) = \kappa$ and $A \subseteq \kappa$), and $A \in U(\kappa, \beta)$ by hypothesis. $\blacksquare$

Compare this with the addability lemma for $\mathcal{A}$ ([[Chapter 1 - Measure Sequences#^lem-1-4-6|Lemma 1.4.6]]): there, the conclusion came from the definition of a $j$-sequence (membership of initial segments in $M$); here it is one line of coherence. Iterating Lemma 5.1.2 over $\beta < o^{\vec{U}}(\nu)$ (using $\kappa$-completeness and the splitting of Lemma 5.3.1 below) gives the exact substitute for addability: every $A \in \bigcap \vec{U}(\kappa)$ can be shrunk, staying in $\bigcap \vec{U}(\kappa)$, so that every $\nu \in A$ with $o^{\vec{U}}(\nu) > 0$ satisfies $A \cap \nu \in \bigcap \vec{U}(\nu)$.

## 5.2 The forcing $\mathbb{P}_{\vec{U}}$

Fix a coherent sequence $\vec{U}$ with $\ell^{\vec{U}} = \kappa + 1$ and $o^{\vec{U}}(\kappa) = \delta > 0$. For an ordinal $d = \nu$ or a pair $d = \langle \nu, B \rangle$ we write $\kappa(d) = \nu$.

>[!definition] Definition 5.2.1 (Gitik, Definition 5.22).
>$\mathbb{P}_{\vec{U}}$ is the set of finite sequences $\langle d_1, \dots, d_n, \langle \kappa, A \rangle \rangle$ such that:
>(1) $A \in \bigcap \vec{U}(\kappa)$;
>(2) $\min(A) > \kappa(d_n)$;
>(3) for every $m$ with $1 \leq m \leq n$, either
>   (3a) $d_m$ is an ordinal and $o^{\vec{U}}(d_m) = 0$, or
>   (3b) $d_m = \langle \nu, A_\nu \rangle$ for some $\nu$ with $o^{\vec{U}}(\nu) > 0$ and $A_\nu \in \bigcap_{\alpha < o^{\vec{U}}(\nu)} U(\nu, \alpha)$;
>(4) for every $1 \leq i \leq j \leq n$,
>   (4a) $\kappa(d_i) < \kappa(d_j)$, and
>   (4b) if $d_j = \langle \nu, A_\nu \rangle$ then $\min(A_\nu) > \kappa(d_i)$.
> ^def-5-2-1

>[!definition] Definition 5.2.2 (Gitik, Definition 5.23).
>Let $p = \langle d_1, \dots, d_n, \langle \kappa, A \rangle \rangle$ and $q = \langle e_1, \dots, e_m, \langle \kappa, B \rangle \rangle$ be in $\mathbb{P}_{\vec{U}}$. We say that $p$ is **stronger** than $q$ and write $p \leq q$ iff
>(1) $A \subseteq B$;
>(2) $n \geq m$;
>(3) there are $1 \leq i_1 < \dots < i_m \leq n$ such that for every $k$, $1 \leq k \leq m$, either
>    (3a) $e_k = d_{i_k}$, or
>    (3b) $e_k = \langle \nu, B_\nu \rangle$ and $d_{i_k} = \langle \nu, C_\nu \rangle$ with $C_\nu \subseteq B_\nu$;
>(4) with $i_1, \dots, i_m$ as in (3), for every $j$, $1 \leq j \leq n$, with $j \notin \{i_1, \dots, i_m\}$:
>    (4a) if $j > i_m$, then $d_j \in B$, or $d_j = \langle \nu, C_\nu \rangle$ with $\nu \in B$ and $C_\nu \subseteq B \cap \nu$;
>    (4b) if $j < i_m$, then for the least $k$ with $j < i_k$, $e_k$ is of the form $\langle \nu, B_\nu \rangle$, and
>    $\quad$(i) if $d_j$ is an ordinal, then $d_j \in B_\nu$;
>    $\quad$(ii) if $d_j = \langle \rho, S \rangle$, then $\rho \in B_\nu$ and $S \subseteq B_\nu$.
> ^def-5-2-2

>[!definition] Definition 5.2.3 (Gitik, Definition 5.24).
>$p$ is a **direct extension** of $q$, written $p \leq^* q$, iff $p \leq q$ and $n = m$ (same stem, shrunken measure-one sets).
> ^def-5-2-3

These are verbatim the definitions of $\mathbb{R}_{\vec{V}}$ ([[Chapter 2 - The Radin Forcing#^def-2-2-1|Definitions 2.2.1]]–[[Chapter 2 - The Radin Forcing#^def-2-2-3|2.2.3]]), with the measure sequences $\vec{F}_\nu$ and $\vec{V}$ deleted from the conditions: a triple $\langle \nu, \vec{F}_\nu, A_\nu \rangle$ becomes a pair $\langle \nu, A_\nu \rangle$, the sequence $\vec{F}_\nu$ being recovered from $\vec{U}$ as $\vec{U}(\nu)$. As always, our $p \leq q$ means $p$ stronger, the reverse of Gitik's convention.

## 5.3 Splitting and the transfer theorem

>[!lemma] Lemma 5.3.1 (Gitik; the splitting).
>Suppose $\delta = o^{\vec{U}}(\kappa) < \kappa$. For each $\alpha < \delta$ let $Y_\alpha = \{\nu < \kappa \mid o^{\vec{U}}(\nu) = \alpha\}$. Then the $Y_\alpha$'s are pairwise disjoint and $Y_\alpha \in U(\kappa, \alpha)$.
> ^lem-5-3-1

*Proof.* Disjointness is immediate since $o^{\vec{U}}$ is a function. For $Y_\alpha \in U(\kappa, \alpha)$, let $j = j^\kappa_\alpha : V \to M$; by coherence $j(\vec{U}) \upharpoonright \kappa + 1 = \vec{U} \upharpoonright (\kappa, \alpha)$, so $o^{j(\vec{U})}(\kappa) = \alpha$. By Łoś, $Y_\alpha = \{\nu < \kappa \mid o^{\vec{U}}(\nu) = \alpha\} \in U(\kappa, \alpha)$ iff in $M$, $o^{j(\vec{U})}(\kappa) = \alpha$, which is exactly what coherence gives. $\blacksquare$

>[!theorem] Theorem 5.3.2 (Gitik, p. 1419).
>All the results of Chapters 2–4 are valid with $\mathbb{P}_{\vec{U}}$ replacing $\mathbb{R}_{\vec{V}}$: the $\kappa^+$-c.c. ([[Chapter 2 - The Radin Forcing#^lem-2-4-1|Lemma 2.4.1]]), factorization ([[Chapter 2 - The Radin Forcing#^lem-2-4-2|Lemma 2.4.2]]), the closure of $\leq^*$ ([[Chapter 2 - The Radin Forcing#^lem-2-4-3|Lemma 2.4.3]]), the Prikry property ([[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]]), cardinal preservation ([[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]]), the club $C_G$ and its order-type analysis with the resulting cofinality classification ([[Chapter 3 - The Radin Club and Changes of Cofinality#^lem-3-1-2|Lemmas 3.1.2]]–[[Chapter 3 - The Radin Club and Changes of Cofinality#^thm-3-3-2|Theorem 3.3.2]]), and the preservation results of Chapter 4 ([[Chapter 4 - Preserving Large Cardinals#^thm-4-2-1|Theorems 4.2.1]] and [[Chapter 4 - Preserving Large Cardinals#^thm-4-4-1|4.4.1]], the latter under the evident reformulation: $\mathrm{cf}(o^{\vec{U}}(\kappa)) \geq \kappa^+$). The proofs require only trivial changes.
> ^thm-5-3-2

*Proof (translation guide).* The proofs of Chapters 2–4 use the ambient embedding $j$ only through three features of the measure sequences, each of which coherence supplies directly:

1. **Membership in $\mathcal{A}$.** Whenever a point $\langle \nu, \vec{F}_\nu \rangle$ was drawn from a measure-one set, we used $\langle \nu, \vec{F}_\nu \rangle \in \mathcal{A}$ to know that the construction could be continued below $\nu$. For $\mathbb{P}_{\vec{U}}$, the continuation below $\nu$ uses $\vec{U}(\nu)$, which needs no certification.
2. **Addability.** Every use of "shrink $A$ so that $A \cap V_\nu \in \bigcap \vec{F}_\nu$ for every pair in $A$" ([[Chapter 1 - Measure Sequences#^lem-1-4-6|Lemma 1.4.6]]) is replaced by Lemma 5.1.2 and its iterated form.
3. **Ultrapower computations.** Statements evaluated in $M$ via "$X \in U(\alpha) \iff \vec{V} \upharpoonright \alpha \in j(X)$" (e.g. in the proof of the Prikry property) become Łoś computations in $\mathrm{Ult}(V, U(\kappa, \alpha))$, with coherence providing the agreement $j^\kappa_\alpha(\vec{U}) \upharpoonright \kappa + 1 = \vec{U} \upharpoonright (\kappa, \alpha)$.

With these substitutions the arguments go through word for word; in fact they simplify, since measure-one sets consist of ordinals only. $\blacksquare$

>[!exercise] Exercise 5.3.3 (guided).
>Carry out the translation in detail for the Prikry property: state and prove the $\mathbb{P}_{\vec{U}}$-version of [[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]]. (Hint: the sets $\tilde{A}(\vec{d})$ and the three cases of the proof are unchanged; wherever the original proof picks a pair addible to a condition, apply the iterated form of Lemma 5.1.2.)
> ^ex-5-3-3

>[!corollary] Corollary 5.3.4 (Gitik, p. 1419).
>Suppose $\delta = o^{\vec{U}}(\kappa) < \kappa$. Above the condition $\langle \langle \kappa, \bigcup_{\alpha < \delta} Y_\alpha \rangle \rangle$, the forcing $\mathbb{P}_{\vec{U}}$ is the Magidor forcing for changing the cofinality of $\kappa$ to $\mathrm{cf}(\delta)$; it preserves cardinals, adds no bounded subsets of $\kappa$, and forces $\mathrm{cf}(\kappa) = \mathrm{cf}(\delta)^V$ from the hypothesis $o(\kappa) = \delta$ alone.
> ^cor-5-3-4

*Proof.* By Lemma 5.3.1, $\bigcup_{\alpha < \delta} Y_\alpha \in \bigcap \vec{U}(\kappa)$, so the displayed object is a condition; below it, every pair $\langle \nu, A_\nu \rangle$ in a stem has $\nu \in \bigcup_\alpha Y_\alpha$, hence carries its assigned measure sequence $\vec{U}(\nu)$ of length $o^{\vec{U}}(\nu) < \kappa$. That this forcing is exactly Magidor's forcing of [37] is the subject of Chapter 6; the preservation and cofinality claims are instances of Theorem 5.3.2 together with [[Chapter 3 - The Radin Club and Changes of Cofinality#^thm-3-2-5|Theorem 3.2.5]]. $\blacksquare$

---

## Notes

Definition 5.1.1, Definitions 5.2.1–5.2.3, Lemma 5.3.1, Theorem 5.3.2 and Corollary 5.3.4 correspond to Gitik's Definition 5.21, Definitions 5.22–5.24, and the discussion on p. 1419 ("all the results of the previous section are valid in the present context with $\mathbb{P}_{\vec{U}}$ replacing $\mathbb{R}_{\vec{V}}$... the proofs require only trivial changes"). Coherent sequences were introduced by Mitchell [43]; the observation that Radin forcing can be built on them — replacing the embedding $j : V \to M$ — is Mitchell's [42], and its main advantage is the reduction of the initial hypotheses, which also yields equiconsistency results. Magidor's forcing [37] was originally defined directly from a Mitchell-increasing sequence of measures; Corollary 5.3.4 is Gitik's way of recovering it inside $\mathbb{P}_{\vec{U}}$. Lemma 5.1.2 is the coherence substitute for addability that makes the transfer literal rather than heuristic. Merimovich's extender-based Radin forcing [39], which combines the present construction with the extender-based Prikry forcing of Gitik's Section 3, is discussed briefly in Chapter 7.

## References

Main reference:

- Moti Gitik. Prikry-type forcings. In Matthew Foreman and Akihiro Kanamori, editors, *Handbook of Set Theory*, pages 1351–1447. Springer, Dordrecht, 2010.

Numbering below follows the bibliography of Gitik's chapter:

- [37] Menachem Magidor. Changing cofinality of cardinals. *Fundamenta Mathematicae*, 99(1):61–71, 1978.
- [39] Carmi Merimovich. Extender-based Radin forcing. *Transactions of the American Mathematical Society*, 355(5):1729–1772, 2003.
- [42] William J. Mitchell. How weak is a closed unbounded ultrafilter? In *Logic Colloquium '80 (Prague, 1980)*, volume 108 of Studies in Logic and the Foundations of Mathematics, pages 209–230. North-Holland, Amsterdam, 1982.
- [43] William J. Mitchell. The core model for sequences of measures. I. *Mathematical Proceedings of the Cambridge Philosophical Society*, 95(2):229–260, 1984.


In 1978 Magidor [37] constructed the first forcing that changes the cofinality of a cardinal $\kappa$ to an *uncountable* value $\delta < \kappa$ without collapsing cardinals. His initial assumption was a sequence $\langle U_\gamma \mid \gamma < \delta \rangle$ of normal measures on $\kappa$, increasing in the Mitchell order — in modern terms, the top row of a coherent sequence with $o(\kappa) = \delta$. We present the forcing twice: first as a cone of the forcing $\mathbb{P}_{\vec{U}}$ of Chapter 5, where all of its properties are inherited for free; then in Magidor's original direct form, which is the version used in applications. We then explain why the Mitchell-order hypothesis suffices here, in contrast with the Radin forcing $\mathbb{R}_{\vec{V}}$, and discuss the optimality of that hypothesis.

## 6.1 Magidor forcing as a cone of $\mathbb{P}_{\vec{U}}$

Fix a coherent sequence of measures $\vec{U}$ with $\ell^{\vec{U}} = \kappa + 1$ and $o^{\vec{U}}(\kappa) = \delta$, where $0 < \delta < \kappa$ ([[Chapter 5 - Coherent Sequences of Measures#^def-5-1-1|Definition 5.1.1]]). Recall the splitting of [[Chapter 5 - Coherent Sequences of Measures#^lem-5-3-1|Lemma 5.3.1]]: the sets
$$Y_\alpha = \{\nu < \kappa \mid o^{\vec{U}}(\nu) = \alpha\}, \qquad \alpha < \delta,$$
are pairwise disjoint and $Y_\alpha \in U(\kappa, \alpha)$. In particular $\bigcup_{\alpha < \delta} Y_\alpha \in \bigcap \vec{U}(\kappa)$.

>[!definition] Definition 6.1.1 (Gitik, p. 1419).
>The **Magidor forcing** associated with $\vec{U}$ is the cone
>$$\mathbb{M}_{\vec{U}} = \mathbb{P}_{\vec{U}} \upharpoonright \langle \langle \kappa, {\textstyle\bigcup_{\alpha < \delta}} Y_\alpha \rangle \rangle,$$
>i.e. the forcing $\mathbb{P}_{\vec{U}}$ ([[Chapter 5 - Coherent Sequences of Measures#^def-5-2-1|Definitions 5.2.1]]–[[Chapter 5 - Coherent Sequences of Measures#^def-5-2-3|5.2.3]]) below the displayed condition, with the induced orders $\leq$ and $\leq^*$.
> ^def-6-1-1

Since the $Y_\alpha$'s are disjoint, every point $\nu$ appearing in a stem of a condition in $\mathbb{M}_{\vec{U}}$ carries a well-defined **index**, namely $\alpha = o^{\vec{U}}(\nu)$: ordinal entries $d_m$ (case (3a) of [[Chapter 5 - Coherent Sequences of Measures#^def-5-2-1|Definition 5.2.1]]) are the points of index $0$, and a pair $\langle \nu, A_\nu \rangle$ is a point of index $o^{\vec{U}}(\nu) > 0$. A stem is therefore nothing but a finite increasing sequence of *indexed points* $\langle (\nu_1, \alpha_1), \dots, (\nu_n, \alpha_n) \rangle$ together with measure-one sets — which is exactly the shape of Magidor's original conditions.

>[!lemma] Lemma 6.1.2 (Canonical refinement).
>Every condition of $\mathbb{M}_{\vec{U}}$ has a direct extension $p$ such that
>1. the top measure-one set $B$ of $p$ satisfies $B \subseteq \bigcup_{\alpha < \delta} Y_\alpha$, and
>2. for every pair $\langle \nu, A_\nu \rangle$ in the stem of $p$, $A_\nu \subseteq \bigcup_{\beta < o^{\vec{U}}(\nu)} Y_\beta \cap \nu$.
> ^lem-6-1-2

*Proof.* Both shrinkings are legitimate for $\leq^*$: for (2), apply [[Chapter 5 - Coherent Sequences of Measures#^lem-5-3-1|Lemma 5.3.1]] at $\nu$ instead of $\kappa$ — the set $Y_\beta \cap \nu = \{\mu < \nu \mid o^{\vec{U}}(\mu) = \beta\}$ lies in $U(\nu, \beta)$ for each $\beta < o^{\vec{U}}(\nu)$, and $A_\nu \in \bigcap_{\beta < o^{\vec{U}}(\nu)} U(\nu, \beta)$; intersecting finitely many measure-one sets stays in the intersection. For (1) there is nothing to do beyond the cone condition itself. $\blacksquare$

The point of the refinement is this: below $p$, any point inserted into the block of a pair $\langle \nu, A_\nu \rangle$ lies in $A_\nu$, hence has index $< o^{\vec{U}}(\nu)$. So *the block below a stem point of index $\alpha$ only ever acquires points of index $< \alpha$* — a self-similar, downward-nested structure governed entirely by the indices. Magidor's original definition builds this in from the start by recording the index of each stem point explicitly.

## 6.2 Magidor's original definition

Let $\delta < \kappa$ and let $\vec{U} = \langle U_\gamma \mid \gamma < \delta \rangle$ be a sequence of normal measures on $\kappa$, increasing in the Mitchell order $\lhd$. (Such a sequence exists iff $o(\kappa) \geq \delta$; it is the top row $\vec{U}(\kappa)$ of any coherent sequence with $o^{\vec{U}}(\kappa) = \delta$.) For $\mu < \nu < \delta$, choose a function $f^\nu_\mu : \kappa \to V$ representing $U_\mu$ in the ultrapower by $U_\nu$:
$$[f^\nu_\mu]_{U_\nu} = U_\mu.$$
Such functions exist precisely because $U_\mu \lhd U_\nu$ means $U_\mu \in \mathrm{Ult}(V, U_\nu)$. We write $\vec{f} = \langle f^\nu_\mu \mid \mu < \nu < \delta \rangle$.

The functions $f^\nu_\mu$ allow the measures below a point $\rho < \kappa$ to be *decoded*: for $U_\nu$-almost all $\rho$, the objects $f^\nu_\mu(\rho)$ are normal measures on $\rho$ which cohere with the $f$'s exactly as the $U_\mu$'s cohere among themselves. This is the content of the next lemma, due to Magidor.

>[!lemma] Lemma 6.2.1 (Magidor [37]; the good sets).
>For $0 < \gamma < \delta$, the following sets belong to $U_\gamma$:
>$$A_\gamma = \{\rho < \kappa \mid \forall \mu < \nu < \gamma\ f^\gamma_\mu(\rho) \lhd f^\gamma_\nu(\rho)\ \text{are normal ultrafilters over } \rho\},$$
>$$B_\gamma = \{\rho \in A_\gamma \mid \forall \mu < \nu < \gamma\ [f^\nu_\mu \upharpoonright \rho]_{f^\gamma_\nu(\rho)} = f^\gamma_\mu(\rho)\},$$
>and $B_0 = \{\rho < \kappa \mid \rho \text{ is inaccessible}\} \in U_0$.
> ^lem-6-2-1

*Proof sketch.* Both statements are Łoś computations in $M_\gamma = \mathrm{Ult}(V, U_\gamma)$. For $\rho = \kappa$, the defining clauses of $A_\gamma$ read "$f^\gamma_\mu(\kappa)^{M_\gamma} \lhd f^\gamma_\nu(\kappa)^{M_\gamma}$ are normal ultrafilters over $\kappa$", i.e. "$U_\mu \lhd U_\nu$ are normal ultrafilters over $\kappa$", which hold in $M_\gamma$ since the $U_\mu$'s for $\mu < \gamma$ are elements of $M_\gamma$ by the choice of the representing functions. Similarly, the clause defining $B_\gamma$ at $\rho = \kappa$ reads $[j_\gamma(f^\nu_\mu) \upharpoonright \kappa]_{U_\nu} = [f^\nu_\mu]_{U_\nu} = U_\mu = [f^\gamma_\mu]_{U_\gamma}$, again true in $M_\gamma$. We leave the verification of the details as an exercise. $\blacksquare$

For $\rho \in B_\gamma$, the measures $f^\gamma_\mu(\rho)$ ($\mu < \gamma$) on $\rho$ are the exact analogue of the sequence $\vec{U}(\rho)$ of Chapter 5 — obtained here by explicit decoding rather than by coherence. We can now define the forcing, following Magidor [37]; our notation follows the restatement by Fuchs.

>[!definition] Definition 6.2.2 (Neighbor functions).
>For a finite $a \subseteq \delta$ define $l_a : \delta \to \delta \cup \{-1\}$ and $r_a : \delta \to \delta + 1$ by
>$$l_a(\gamma) = \max(a \cap \gamma) \ (\text{or } {-1}\text{ if } a \cap \gamma = \varnothing), \qquad r_a(\gamma) = \min\big((a \cup \{\delta\}) \setminus (\gamma + 1)\big),$$
>the nearest neighbors of $\gamma$ inside $a$, to the left and to the right.
> ^def-6-2-2

>[!definition] Definition 6.2.3 (Magidor [37]).
>The **Magidor forcing** $\mathbb{M}(\vec{U}, \vec{f})$ consists of pairs $\langle g, G \rangle$ such that
>1. $\mathrm{dom}(g)$ is a finite subset of $\delta$, and $\mathrm{dom}(G) = \delta \setminus \mathrm{dom}(g)$;
>2. for all $\gamma \in \mathrm{dom}(g)$, $g(\gamma) \in B_\gamma$, and $g$ is strictly increasing;
>3. for all $\gamma \in \mathrm{dom}(G)$, if $\theta = r_{\mathrm{dom}(g)}(\gamma) < \delta$ then $G(\gamma) \in f^\theta_\gamma(g(\theta))$, and if $\theta = \delta$ then $G(\gamma) \in U_\gamma$;
>4. if $\gamma < \xi < \delta$ with $\gamma \in \mathrm{dom}(g)$ and $\xi \in \mathrm{dom}(G)$, then $g(\gamma) \cap G(\xi) = \varnothing$.
>
>The ordering is defined by $\langle g', G' \rangle \leq \langle g, G \rangle$ ($g'$ stronger) iff
>1. $g \subseteq g'$;
>2. $G'(\gamma) \subseteq G(\gamma)$ for all $\gamma \in \mathrm{dom}(G')$;
>3. $g'(\gamma) \in G(\gamma)$ for all $\gamma \in \mathrm{dom}(g') \setminus \mathrm{dom}(g)$.
>
>We write $\langle g', G' \rangle \leq^* \langle g, G \rangle$ (**direct extension**) iff $\langle g', G' \rangle \leq \langle g, G \rangle$ and $g' = g$.
> ^def-6-2-3

Thus $g$ is the stem: a finite increasing sequence of points, each tagged with its index $\gamma$, chosen from the good set $B_\gamma$. Clause (3) says that a measure-one set at an unused index $\gamma$ is measured by $f^\theta_\gamma(g(\theta))$ — the $\gamma$-th measure on $\rho = g(\theta)$, where $(\rho, \theta)$ is the nearest stem point *above* $\gamma$; if there is none, the ambient measure $U_\gamma$ is used. Clause (4) guarantees that a new point inserted at index $\gamma$ lands in the interval $\big(g(l(\gamma)),\, g(r(\gamma))\big)$ determined by its stem neighbors, so that $g'$ remains strictly increasing. Note that, in parallel with the rest of these notes, $\leq$ means "stronger than"; Magidor's and Gitik's papers use the opposite convention. In some presentations one additionally fixes an ordinal $\tilde{\alpha} < \kappa$ and requires all stem points to exceed $\tilde{\alpha}$ (the "forcing above $\tilde{\alpha}$"); this freedom is useful in iteration arguments but plays no role here.

>[!definition] Definition 6.2.4.
>Let $G \subseteq \mathbb{M}(\vec{U}, \vec{f})$ be generic over $V$. The **Magidor sequence** is
>$$c_G(\gamma) = g(\gamma) \quad\text{for the unique value forced by any } \langle g, G \rangle \in G \text{ with } \gamma \in \mathrm{dom}(g).$$
> ^def-6-2-4

>[!lemma] Lemma 6.2.5.
>The Magidor sequence $c_G : \delta \to \kappa$ is defined on all of $\delta$, strictly increasing, continuous at limit ordinals, and cofinal in $\kappa$. In particular its range is a closed unbounded subset of $\kappa$ of order type $\delta$ (for $\delta$ a limit ordinal).
> ^lem-6-2-5

*Proof sketch.* Totality is a density argument: given $\langle g, G \rangle$ and $\gamma \notin \mathrm{dom}(g)$, with $\theta = r_{\mathrm{dom}(g)}(\gamma)$, any $\rho \in G(\gamma)$ above the current stem values below $\gamma$ yields a stronger condition $\langle g \cup \{\langle \gamma, \rho \rangle\}, G' \rangle$ — the side conditions of Definition 6.2.3 hold by clauses (3) and (4) for $\langle g, G \rangle$. Monotonicity is built into clause (2). Cofinality: for $\gamma$ with no stem point above, $G(\gamma) \in U_\gamma$ is unbounded in $\kappa$, so values at index $\gamma$ are forced unboundedly high. Continuity at a limit $\lambda$: if $\lambda \in \mathrm{dom}(g)$, then for every $\xi \in \big(l_{\mathrm{dom}(g)}(\lambda), \lambda\big)$ the set $G(\xi)$ is measure one for the normal ultrafilter $f^\lambda_\xi(g(\lambda))$ over $g(\lambda)$, hence unbounded in $g(\lambda)$; inserting points at larger and larger indices below $\lambda$ therefore forces $\sup_{\gamma < \lambda} c_G(\gamma) = c_G(\lambda)$. A continuous strictly increasing function has closed range, and a strictly increasing function on $\delta$ has range of order type $\delta$. $\blacksquare$

>[!exercise] Exercise 6.2.6.
>Spell out the correspondence between $\mathbb{M}(\vec{U}, \vec{f})$ and the cone $\mathbb{M}_{\vec{U}}$ of [[#^def-6-1-1|Definition 6.1.1]]: given a condition $\langle g, G \rangle$ with $\mathrm{dom}(g) = \{\gamma_1 < \dots < \gamma_n\}$, describe the associated condition of $\mathbb{P}_{\vec{U}}$ whose stem pairs are $\langle g(\gamma_i), A_{g(\gamma_i)} \rangle$ with $A_{g(\gamma_i)} = \bigcap_{\xi < \gamma_i} G'(\xi)$, where the $G'(\xi)$ are the appropriate shrinkings of the $G(\xi)$'s. Show that the values of the Magidor sequence are exactly the pair coordinates appearing in stems of the generic for the cone, and conclude (using [[Chapter 3 - The Radin Club and Changes of Cofinality#^lem-3-1-3|Lemma 3.1.3]] and [[#^lem-6-2-5|Lemma 6.2.5]]) that $\mathrm{ran}(c_G)$ is club in $\kappa$ and computes $\mathrm{cf}(\kappa)$ in the extension.
> ^ex-6-2-6

## 6.3 The main theorem

>[!theorem] Theorem 6.3.1 (Magidor [37]).
>Let $\delta < \kappa$ and let $\vec{U} = \langle U_\gamma \mid \gamma < \delta \rangle$ be a $\lhd$-increasing sequence of normal measures on $\kappa$. Set $\mathbb{M} = \mathbb{M}(\vec{U}, \vec{f})$. Then:
>1. $\langle \mathbb{M}, \leq, \leq^* \rangle$ has the Prikry property, and $\leq^*$ is $\kappa$-closed;
>2. $\mathbb{M}$ has the $\kappa^+$-chain condition;
>3. $\mathbb{M}$ preserves all cardinals and adds no bounded subsets of $\kappa$;
>4. $\Vdash_{\mathbb{M}} \mathrm{cf}(\kappa) = \mathrm{cf}(\delta)^V$.
> ^thm-6-3-1

*Proof.* All parts are inherited from the coherent-sequence forcing of Chapter 5 via the cone presentation of Section 6.1. Extend $\vec{U}$ to a coherent sequence with $o^{\vec{U}}(\kappa) = \delta$ (possible since $o(\kappa) \geq \delta$; see the discussion after [[Chapter 5 - Coherent Sequences of Measures#^def-5-1-1|Definition 5.1.1]]). The cone $\mathbb{M}_{\vec{U}}$ is a subordering of $\mathbb{P}_{\vec{U}}$, so the transfer theorem [[Chapter 5 - Coherent Sequences of Measures#^thm-5-3-2|Theorem 5.3.2]] applies to it directly:

1. The Prikry property is the $\mathbb{P}_{\vec{U}}$-version of [[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]], and the $\kappa$-closure of $\leq^*$ is that of [[Chapter 2 - The Radin Forcing#^lem-2-4-3|Lemma 2.4.3]] — in the cone the argument only simplifies, since measure-one sets consist of ordinals.
2. The $\kappa^+$-c.c. is [[Chapter 2 - The Radin Forcing#^lem-2-4-1|Lemma 2.4.1]]: conditions are finite sequences of objects from $V_{\kappa+1}$ of size $\leq \kappa$ after fixing the stem, so any two conditions with the same stem are compatible.
3. Cardinal preservation now follows by the standard argument of [[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]]: the $\kappa^+$-c.c. preserves cardinals $\geq \kappa^+$, and the Prikry property together with $\kappa$-closure of $\leq^*$ shows no new bounded subsets of $\kappa$ are added, preserving cardinals $\leq \kappa$.
4. By [[#^lem-6-2-5|Lemma 6.2.5]], $c_G : \delta \to \kappa$ is continuous and cofinal, so $\mathrm{cf}^{V[G]}(\kappa) = \mathrm{cf}^{V[G]}(\delta)$. Since $\delta < \kappa$ and no bounded subsets of $\kappa$ are added, $\mathrm{cf}^{V[G]}(\delta) = \mathrm{cf}^V(\delta)$. (Equivalently, in the cone presentation, the order-type analysis of [[Chapter 3 - The Radin Club and Changes of Cofinality#^thm-3-2-5|Theorem 3.2.5]] gives $\mathrm{cf}(\kappa) = \mathrm{cf}(\omega^\delta) = \mathrm{cf}(\delta)$ directly.) $\blacksquare$

>[!exercise] Exercise 6.3.2 (guided).
>Prove parts (1) and (2) of Theorem 6.3.1 directly from Definition 6.2.3, without passing through $\mathbb{P}_{\vec{U}}$. Hints: for the closure of $\leq^*$, intersect fewer than $\kappa$ many measure-one sets index by index (each $f^\theta_\gamma(g(\theta))$ is $g(\theta)$-complete and there are only $|\delta| < \kappa$ many indices); for the Prikry property, imitate the proof of [[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]] with the stem $g$ in place of $d_1, \dots, d_n$ — the relevant partition argument takes place, for each stem point $g(\theta)$, inside the measures $f^\theta_\gamma(g(\theta))$ for $\gamma < \theta$.
> ^ex-6-3-2

## 6.4 Why Mitchell order suffices: comparison with $\mathbb{R}_{\vec{V}}$

It is worth pausing on exactly why Magidor forcing runs on the cheap hypothesis $o(\kappa) = \delta$, while the parallel cofinality change via $\mathbb{R}_{\vec{V}}$ requires a measure sequence of length $\delta$ in $\mathcal{A}$ — already length $2$ costs a μ-measurable cardinal ([[Chapter 1 - Measure Sequences#^def-1-6-3|Definition 1.6.3]]), and length $\geq \kappa^+$ costs much more ([[Chapter 1 - Measure Sequences#^lem-1-5-1|Lemma 1.5.1]]).

1. **The measures concentrate on ordinals.** Every measure used in $\mathbb{M}(\vec{U}, \vec{f})$ — the $U_\gamma$'s, the decoded measures $f^\theta_\gamma(\rho)$ — is an ultrafilter over an *ordinal*, and measure-one sets consist of ordinals. In $\mathbb{R}_{\vec{V}}$, by contrast, a measure-one set consists of pairs $\langle \nu, \vec{F}_\nu \rangle$, i.e. of elements of $V_\kappa$ carrying their own measure sequences.
2. **Stem points do not spawn nested blocks of new measure sequences.** Inserting a point $\rho$ at index $\gamma$ into a Magidor stem commits us to nothing below $\rho$ except the measures $f^\gamma_\mu(\rho)$ for $\mu < \gamma$, all of which are decoded from the ambient functions $f$ — the recursion bottoms out at ordinals. In $\mathbb{R}_{\vec{V}}$, inserting $\langle \nu, \vec{F}_\nu \rangle$ imports the whole sequence $\vec{F}_\nu$, whose own measure-one sets again consist of pairs, and so on; this is why the membership $\langle \nu, \vec{F}_\nu \rangle \in \mathcal{A}$ had to be certified by a constructing embedding ([[Chapter 1 - Measure Sequences#^def-1-4-2|Definition 1.4.2]]).
3. **The strength accounting.** A $\lhd$-increasing sequence of length $\delta$ over $\kappa$ exists as soon as $o(\kappa) \geq \delta$ — pure Mitchell order, no extenders; by Mitchell's core model theory [43], the assertion "$o(\kappa) = \delta$" is equiconsistent with its forcing consequences. The measure sequences of Chapter 1 live strictly higher: μ-measurability is the weakest large cardinal property requiring extenders not equivalent to normal ultrafilters ([[Chapter 1 - Measure Sequences#^def-1-6-3|Section 1.6]]).

So Magidor forcing is the optimal-strength route to $\mathrm{cf}(\kappa) = \delta > \omega$: nothing beyond the canonical inner-model content of "$o(\kappa) = \delta$" is used.

## 6.5 Optimality of the hypotheses

>[!remark] Remark 6.5.1 (stated without proof).
>The conclusion of Theorem 6.3.1 is optimal in two senses.
>
>1. **Bounded subsets are unavoidable over the core model.** Mitchell [45] showed: if the ground model is the core model $K$, then any cardinal-preserving extension changing the cofinality of $\kappa$ to an uncountable $\delta < \kappa$ must add new bounded subsets of $\kappa$. Thus the combination "cardinal preservation + no new bounded subsets + $\mathrm{cf}(\kappa) = \delta > \omega$" necessarily requires a *prepared* ground model: such models were constructed by Mitchell [44] using inner model techniques, and by a pure forcing construction of Gitik [13].
>2. **The assumption $o(\kappa) = \delta$ is necessary.** By Mitchell's analysis of the core model for sequences of measures [43], changing the cofinality of $\kappa$ to $\delta$ while preserving cardinals requires $o^K(\kappa) \geq \delta$ in the core model. Hence Magidor's hypothesis is exactly the consistency strength of the conclusion.
> ^rem-6-5-1

Compare the discussion after [[Chapter 3 - The Radin Club and Changes of Cofinality#^thm-3-2-5|Theorem 3.2.5]]: the Radin club itself adds bounded subsets of $\kappa$ below every pair coordinate, in line with Mitchell's theorem — avoiding them is a matter of preparing the ground model, not of choosing a cleverer forcing.

---

## Notes

The cone presentation of Section 6.1 is Gitik's, from the paragraph on p. 1419 of the Handbook chapter: "If $\delta < \kappa$, then $\langle U(\kappa, \alpha) \mid \alpha < \delta \rangle$ can be split... $\mathbb{P}_{\vec{U}}$, above the condition $\langle \langle \kappa, \bigcup_{\alpha < \delta} Y_\alpha \rangle \rangle$ is then the Magidor forcing for changing cofinality of $\kappa$ to $\mathrm{cf}(\delta)$." [[#^lem-6-1-2|Lemma 6.1.2]] makes explicit the refinement implicit in that identification. Section 6.2 presents Magidor's original definition from [37]; our notation follows the restatement in Fuchs' paper (where the forcing is defined with an additional parameter $\tilde{\alpha}$, the "forcing above $\tilde{\alpha}$", and $\mathbb{M}(\vec{U}, \vec{f}) = \mathbb{M}(\vec{U}, \vec{f}, \alpha)$ in his notation). [[#^lem-6-2-1|Lemma 6.2.1]] is Magidor's observation that the sets $A_\gamma, B_\gamma$ are of measure one; [[#^lem-6-2-5|Lemma 6.2.5]] records the standard properties of the Magidor sequence. [[#^thm-6-3-1|Theorem 6.3.1]] is the main theorem of [37]; the inheritance proof given here is available because of the coherent-sequence approach of Mitchell [42, 43] presented in Chapter 5. [[#^rem-6-5-1|Remark 6.5.1]] summarizes Mitchell [44, 45] and Gitik [13], as cited in Gitik's discussion following Theorem 5.12 of the Handbook chapter.

## References

Main reference:

- Moti Gitik. Prikry-type forcings. In Matthew Foreman and Akihiro Kanamori, editors, *Handbook of Set Theory*, pages 1351–1447. Springer, Dordrecht, 2010.

Numbering below follows the bibliography of Gitik's chapter:

- [13] Moti Gitik. Changing cofinalities and the nonstationary ideal. *Israel Journal of Mathematics*, 56(3):280–314, 1986.
- [37] Menachem Magidor. Changing cofinality of cardinals. *Fundamenta Mathematicae*, 99(1):61–71, 1978.
- [42] William J. Mitchell. How weak is a closed unbounded ultrafilter? In *Logic Colloquium '80 (Prague, 1980)*, volume 108 of Studies in Logic and the Foundations of Mathematics, pages 209–230. North-Holland, Amsterdam, 1982.
- [43] William J. Mitchell. The core model for sequences of measures. I. *Mathematical Proceedings of the Cambridge Philosophical Society*, 95(2):229–260, 1984.
- [44] William J. Mitchell. Indiscernibles, skies, and ideals. In *Axiomatic Set Theory (Boulder, Colo., 1983)*, volume 31 of Contemporary Mathematics, pages 161–182. American Mathematical Society, Providence, 1984.
- [45] William J. Mitchell. Applications of the covering lemma for sequences of measures. *Transactions of the American Mathematical Society*, 299(1):41–58, 1987.

Additional reference for the presentation of Section 6.2:

- Gunar Fuchs. On sequences generic in the sense of Magidor. *The Journal of Symbolic Logic*, 79(4):1286–1314, 2014.

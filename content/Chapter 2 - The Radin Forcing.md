
We now define the forcing itself. Throughout this chapter, $\vec{V} = \langle \kappa, U(0), U(1), \dots, U(\alpha), \dots \mid \alpha < \mathrm{length}(\vec{V}) \rangle$ is a measure sequence in $\mathcal{A}$ with $\kappa(\vec{V}) = \kappa$ and $\mathrm{length}(\vec{V}) \geq 1$. (Such sequences are supplied by [[Chapter 1 - Measure Sequences#^lem-1-5-1|Lemma 1.5.1]] under an extender hypothesis, and by [[Chapter 1 - Measure Sequences#^def-1-6-3|Definition 1.6.3]] in length $\geq 2$.) The forcing $\mathbb{R}_{\vec{V}}$ carries two orders $\leq$ and $\leq^*$: as with Prikry forcing, $\leq$ is used to force, while $\leq^*$ provides closure. **Convention on the order.** We write $p \leq q$ when $p$ is *stronger* than $q$; this is the reverse of Gitik's convention.

*Convention.* We identify an ordinal $\nu$ with the trivial sequence $\langle \nu \rangle$; with this convention $\mathcal{A}$ contains the ordinals, and members of measure-one sets are either ordinals or pairs $\langle \nu, \vec{F}_\nu \rangle$. Recall the notation $\bigcap \vec{F}$ ([[Chapter 1 - Measure Sequences#^def-1-4-4|Definition 1.4.4]]) and $\kappa(d)$: for $d$ an ordinal $\nu$, a pair $\langle \nu, \vec{F} \rangle$, or a triple $\langle \nu, \vec{F}, B \rangle$, we write $\kappa(d) = \nu$. For a triple $d = \langle \nu, \vec{F}, B \rangle$ and a set $A$, we write $d \in A$ to mean that the first two coordinates satisfy $\langle \nu, \vec{F} \rangle \in A$. Finally, recall from [[Chapter 1 - Measure Sequences|Chapter 1]] that every measure occurring in a measure sequence is an ultrafilter on the corresponding $V_\nu$; when below we say that $F$ is "a normal measure on $\nu$", this is always shorthand for a normal measure on $V_\nu$ (typically concentrating on ordinals).

---

## 2.1 Two warm-up cases to keep in mind

Before the formal definition, let us describe informally what a condition should look like in the two simplest cases; the notation here is temporary, and everything is defined formally in Section 2.2.

**The case $\mathrm{length}(\vec{V}) = 1$.** Here $\vec{V} = \langle \kappa, U(0) \rangle$ with $U(0)$ a normal measure on $V_\kappa$ concentrating on ordinals. To singularize $\kappa$ we build an $\omega$-sequence: a condition should consist of a finite increasing sequence of ordinals below $\kappa$ — the part of the sequence already chosen — together with a set $A \in U(0)$ from which all future points are to be picked. This is exactly the Prikry forcing with $U(0)$; see [[#^prop-2-3-1|Proposition 2.3.1]].

**The case $\mathrm{length}(\vec{V}) = 2$.** Here $\vec{V} = \langle \kappa, U(0), U(1) \rangle$, where $U(1)$ concentrates on pairs $\langle \nu, F \rangle$ with $F$ a normal measure on $V_\nu$. We would like both measures to participate in generating the generic sequence. A condition carries a measure-one set $A \in U(0) \cap U(1)$, and extending it means picking a point $a \in A$ and shrinking $A$. If $a$ is an ordinal, it is simply appended, as in the Prikry case. If $a = \langle \nu, F \rangle$, then $a$ can be appended only when $A \cap V_\nu \in F$; it then enters the stem together with its own **block** $B_\nu \in F$, $B_\nu \subseteq A \cap V_\nu$, from which all future points below $\nu$ must be chosen. Thus $\langle \nu, F \rangle$ behaves autonomously and starts producing its own Prikry sequence for $F$, while above $\nu$ the process continues as before. Generically this yields a cofinal sequence of order type $\omega^2$: $\omega$ many blocks, each of order type $\omega$. The details are in [[#^exmp-2-3-2|Example 2.3.2]].

---

## 2.2 The definition of $\mathbb{R}_{\vec{V}}$

>[!definition] Definition 2.2.1 (Gitik, Definition 5.2).
>Let $\mathbb{R}_{\vec{V}}$ be the set of all finite sequences $\langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$ such that
>(1) $A \in \bigcap \vec{V}$ and $A \subseteq \mathcal{A}$;
>(2) $A \cap V_{\kappa(d_n)+1} = \emptyset$;
>(3) for every $m$ with $1 \leq m \leq n$, either
>   (3a) $d_m$ is an ordinal, or
>   (3b) $d_m = \langle \nu, \vec{F}_\nu, A_\nu \rangle$ for some $\vec{F}_\nu \in \mathcal{A}$, $A_\nu \subseteq \mathcal{A}$, and $A_\nu \in \bigcap \vec{F}_\nu$;
>(4) for every $1 \leq i < j \leq n$,
>   (4a) $\kappa(d_i) < \kappa(d_j)$, and
>   (4b) if $d_j = \langle \nu, \vec{F}_\nu, A_\nu \rangle$ then $A_\nu \cap V_{\kappa(d_i)+1} = \emptyset$.
>
>The sequence $\langle d_1, \dots, d_n \rangle$ is called the **stem** of the condition, $\langle \kappa, \vec{V} \rangle$ the **top**, and $A$ the **measure-one set**. Each $d_m$ of the form $\langle \nu, \vec{F}_\nu, A_\nu \rangle$ will give rise to the Radin forcing $\mathbb{R}_{\vec{F}_\nu}$, with $\vec{F}_\nu$ playing the role of $\vec{V}$.
> ^def-2-2-1

>[!definition] Definition 2.2.2 (Gitik, Definition 5.3).
>Let $p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$ and $q = \langle e_1, \dots, e_m, \langle \kappa, \vec{V} \rangle, B \rangle$ be in $\mathbb{R}_{\vec{V}}$. We say that $p$ is **stronger** than $q$ and write $p \leq q$ iff
>(1) $A \subseteq B$;
>(2) $n \geq m$;
>(3) there are $1 \leq i_1 < i_2 < \dots < i_m \leq n$ such that for every $1 \leq k \leq m$, either
>   (3a) $e_k = d_{i_k}$, or
>   (3b) $e_k = \langle \nu, \vec{F}_\nu, B_\nu \rangle$ and $d_{i_k} = \langle \nu, \vec{F}_\nu, C_\nu \rangle$ with $C_\nu \subseteq B_\nu$;
>(4) with $i_1, \dots, i_m$ as in (3), the following holds for every $j$ with $1 \leq j \leq n$ and $j \notin \{i_1, \dots, i_m\}$:
>   (4a) if $j > i_m$, then $d_j \in B$, or $d_j = \langle \nu, \vec{F}_\nu, C_\nu \rangle$ with $\langle \nu, \vec{F}_\nu \rangle \in B$ and $C_\nu \subseteq B \cap V_\nu$;
>   (4b) if $j < i_m$, then for the least $k$ with $j < i_k$, $e_k$ is of the form $\langle \nu, \vec{F}_\nu, B_\nu \rangle$, and
>       (i) if $d_j$ is an ordinal then $d_j \in B_\nu$;
>       (ii) if $d_j = \langle \rho, \vec{T}, S \rangle$ then $\langle \rho, \vec{T} \rangle \in B_\nu$ and $S \subseteq B_\nu$.
> ^def-2-2-2

*Remark.* Clause (4) governs the **newly added** entries of the stem: (4a) says that entries appended above the last old entry come from the measure-one set $B$ of the top, while (4b) says that an entry inserted before $e_k$ must come from the block $B_\nu$ of the next old entry above it. In particular, an insertion is possible only into the block of a triple. (Recall that our $\leq$ is the reverse of Gitik's: for him $p \leq q$ means that $q$ is stronger.)

>[!definition] Definition 2.2.3 (Gitik, Definition 5.4).
>Let $p, q \in \mathbb{R}_{\vec{V}}$ be as above. We say that $p$ is a **direct extension** of $q$ and write $p \leq^* q$ iff $p \leq q$ and $n = m$.
> ^def-2-2-3

>[!exercise] Exercise 2.2.4.
>Show that $\leq$ and $\leq^*$ are partial orders on $\mathbb{R}_{\vec{V}}$, and that $\leq^* \subseteq \leq$. Show also that $p \leq^* q$ iff $p$ is obtained from $q$ by shrinking the measure-one set and the blocks of the triples of the stem (in particular, the stems have the same length and the same first coordinates).
> ^ex-2-2-4

---

## 2.3 Two examples

>[!proposition] Proposition 2.3.1 (Length one is Prikry forcing).
>Let $\kappa$ be measurable and $U$ a normal measure on $V_\kappa$ concentrating on ordinals; set $\vec{V} = \langle \kappa, U \rangle$ (then $\vec{V} \in \mathcal{A}$ by [[Chapter 1 - Measure Sequences#^exmp-1-6-1|Example 1.6.1]](d)). Let $\mathbf{1}' = \langle \langle \kappa, \vec{V} \rangle, \kappa \rangle$ be the empty-stem condition whose measure-one set consists of all ordinals below $\kappa$. Then
>$$\langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \longmapsto \langle \langle \kappa(d_1), \dots, \kappa(d_n) \rangle, A \rangle$$
>is an isomorphism of $\{p \in \mathbb{R}_{\vec{V}} \mid p \leq \mathbf{1}'\}$ onto the Prikry forcing $\mathbb{P}_U$, with $\leq^*$ corresponding to the Prikry direct extension.
> ^prop-2-3-1

*Proof.* Every $p \leq \mathbf{1}'$ has an ordinal-only stem and $A \subseteq \kappa$: by clause (4a) each stem entry must lie in the measure-one set $\kappa$ of $\mathbf{1}'$, and $\kappa$ contains no pairs. Conversely, every Prikry condition is the image of such a $p$, and clause (2) of [[#^def-2-2-1|Definition 2.2.1]] matches the requirement that the measure-one set lie above the maximum of the stem. The map is therefore a bijection, and it respects the orders: by clause (4b), an entry inserted below the last old entry must come from the block of a triple among the old entries — and there are none — so stems are only end-extended, with new entries taken from the old measure-one set and a shrunken final set. This is exactly the Prikry order. $\blacksquare$

*Remark.* The condition $\mathbf{1}'$ is not the weakest element of $\mathbb{R}_{\vec{V}}$: the condition $\langle \langle \kappa, \vec{V} \rangle, \mathcal{A} \cap V_\kappa \rangle$ is strictly weaker, and below it there are conditions whose stems contain genuine triples $\langle \nu, \vec{F}_\nu, A_\nu \rangle$ coming from smaller measure sequences; such conditions are incompatible with $\mathbf{1}'$. By [[#^lem-2-4-2|Lemma 2.4.2]] below, the forcing below such a condition factors into a smaller Radin forcing times a Prikry tail. So $\mathbb{R}_{\langle \kappa, U \rangle}$ consists of the Prikry part $\{p \mid p \leq \mathbf{1}'\}$ together with side copies of smaller Radin forcings sitting below measurable cardinals $\nu < \kappa$.

>[!example] Example 2.3.2 (Length two, from a μ-measurable cardinal).
>Let $\kappa$ be μ-measurable ([[Chapter 1 - Measure Sequences#^def-1-6-3|Definition 1.6.3]]), witnessed by $j : V \to M$, and let $\vec{V} = \langle \kappa, U(0), U(1) \rangle$ be the derived sequence of length $2$. Then $\vec{V} \in \mathcal{A}$: indeed, $U(1)$ concentrates on pairs $\langle \nu, F \rangle$ with $\nu$ measurable and $F$ a normal measure on $V_\nu$ ([[Chapter 1 - Measure Sequences#^ex-1-6-4|Exercise 1.6.4]]), and every such pair is a measure sequence of length $1$, hence belongs to $\mathcal{A}$ vacuously ([[Chapter 1 - Measure Sequences#^exmp-1-6-1|Example 1.6.1]](d)); so $\mathcal{A} \cap V_\kappa \in U(1)$, while $U(0)$ concentrates on ordinals.
>
>A condition $p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$ therefore consists of a finite stem of ordinals and triples $\langle \nu, F, A_\nu \rangle$ (with $A_\nu \in F$), a top $\langle \kappa, \vec{V} \rangle$, and $A \in U(0) \cap U(1)$, which we may take to consist of ordinals and such pairs. Let us analyze the one-step extensions of $\langle \langle \kappa, \vec{V} \rangle, A \rangle$. An ordinal $a \in A$ is appended freely. A pair $\langle \nu, F \rangle \in A$ can be appended only when $A \cap V_\nu \in F$; this is a measure-one phenomenon: the set
>$$X_A = \{\langle \nu', F' \rangle \mid A \cap V_{\nu'} \in F'\}$$
>lies in $U(1)$, since in $M$ we have $\langle \kappa, U(0) \rangle \in j(X_A)$ iff $j(A) \cap V_\kappa \in U(0)$, and $j(A) \cap V_\kappa = A \in U(0)$. When $A \cap V_\nu \in F$, the triple enters the stem with a block $B_\nu \in F$, $B_\nu \subseteq A \cap V_\nu$, and from then on all points below $\nu$ must come from $B_\nu$: the pair starts its own Prikry sequence for $F$. Above $\nu$ the process continues with the remaining part of $A$.
>
>Let $G$ be generic and let
>$$C_G = \{\kappa(d) < \kappa \mid \exists p \in G\ (d \text{ appears in the stem of } p)\}$$
>be the **Radin club** (studied systematically in the next chapter). The shape of the generic object is as follows.
> ^exmp-2-3-2

>[!proposition] Proposition 2.3.3.
>In the situation of [[#^exmp-2-3-2|Example 2.3.2]]:
>(a) $C_G$ is a closed unbounded subset of $\kappa$;
>(b) a final segment of $C_G$ has order type $\omega^2$;
>(c) the limit points of $C_G$ are exactly those $\nu$ for which a pair $\langle \nu, F_\nu \rangle$ appears in the stem of some $p \in G$; each such $\nu$ is measurable in $V$, and the points of $C_G$ between two consecutive limit points form a Prikry sequence for the corresponding $F_\nu$.
>
>In particular $V[G] \models \mathrm{cf}(\kappa) = \omega$: length $2$ still singularizes $\kappa$ to cofinality $\omega$. Changing the cofinality to an *uncountable* value requires longer sequences and is the subject of the next chapter, where (a)–(c) are proved in full generality.
> ^prop-2-3-3

---

## 2.4 Basic structural properties

We turn to the four lemmas on which the whole theory rests: the chain condition, factorization, closure, and the Prikry property; combined, they give cardinal preservation.

>[!lemma] Lemma 2.4.1 (Gitik, Lemma 5.5).
>$\langle \mathbb{R}_{\vec{V}}, \leq \rangle$ satisfies the $\kappa^+$-c.c.
> ^lem-2-4-1

*Proof.* Two conditions with the same stem and the same top are compatible: intersect the measure-one sets and the blocks of the stem triples; the intersections remain measure one by completeness of the relevant filters. A stem is a finite sequence of elements of $V_\kappa$, and $|V_\kappa| = \kappa$ since $\kappa$ is inaccessible, so there are at most $\kappa$ stems. Hence every antichain has size at most $\kappa$. $\blacksquare$

For the next two lemmas we need some notation. Let $p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle \in \mathbb{R}_{\vec{V}}$ and suppose that for some $m$ with $1 \leq m \leq n$, $d_m = \langle \nu_m, \vec{V}_m, A_m \rangle$ is a triple. Set
$$p^{\leq m} = \langle d_1, \dots, d_m \rangle \quad \text{and} \quad p^{>m} = \langle d_{m+1}, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle.$$
Then $p^{\leq m} \in \mathbb{R}_{\vec{V}_m}$ and $p^{>m} \in \mathbb{R}_{\vec{V}}$. For $\vec{W} \in \mathcal{A}$ and $q \in \mathbb{R}_{\vec{W}}$, write $\mathbb{R}_{\vec{W}}/q = \{r \in \mathbb{R}_{\vec{W}} \mid r \leq q\}$.

>[!lemma] Lemma 2.4.2 (Gitik, Lemma 5.6; Factorization).
>$\mathbb{R}_{\vec{V}}/p \simeq \mathbb{R}_{\vec{V}_m}/p^{\leq m} \times \mathbb{R}_{\vec{V}}/p^{>m}$.
> ^lem-2-4-2

*Proof.* Map $r \in \mathbb{R}_{\vec{V}}/p$ to $(r^{\leq m}, r^{>m})$. By clause (4b) of [[#^def-2-2-2|Definition 2.2.2]], every entry of $r$ inserted below $\nu_m$ comes from the blocks of the triples among $d_1, \dots, d_m$, while by clause (4a) every entry above $\nu_m$ comes from the blocks of $d_{m+1}, \dots, d_n$ or from the top measure-one set; hence the map is a bijection between the cones. That it respects both $\leq$ and $\leq^*$ is immediate from the definition of the order. $\blacksquare$

>[!lemma] Lemma 2.4.3 (Gitik, Lemma 5.7).
>$\langle \mathbb{R}_{\vec{V}}/p^{>m}, \leq^* \rangle$ is $\nu_m$-closed.
> ^lem-2-4-3

*Proof.* Let $\langle r_\xi \mid \xi < \mu \rangle$, $\mu < \nu_m$, be a chain in the cone with $r_\eta \leq^* r_\xi$ for $\xi < \eta$. Direct extensions do not change the length or the first coordinates of the stem, so only the top measure-one set and the blocks of the stem triples shrink. All of these belong to filters that are $\lambda$-complete for some $\lambda > \nu_m$: the top filter $\bigcap \vec{V}$ is $\kappa$-complete, and each stem triple $\langle \nu, \vec{F}_\nu, B_\nu \rangle$ occurring in $p^{>m}$ has $\nu > \nu_m$ and $B_\nu \in \bigcap \vec{F}_\nu$. The entrywise intersections therefore remain measure one, and the condition with the common stem and the intersected sets extends every $r_\xi$. $\blacksquare$

The heart of the matter is the Prikry property. The new point, compared with Prikry forcing, is that a condition may be extended by picking elements from *different* measures $U(\alpha)$ of the sequence $\vec{V}$; one has to show that different choices cannot decide a statement differently — roughly, that one can pass from one choice of a measure to another while staying with compatible conditions.

More precisely, the proof below has exactly the same architecture as the proof of the Prikry property for Prikry forcing — split the possible one-step extensions into three parts according to whether they can be directly extended to decide $\sigma$ or $\neg\sigma$, shrink once by a diagonal intersection, take a decider of minimal length, and derive a contradiction by amalgamating two incompatible decisions — and the reader who knows that proof is encouraged to reconstruct this one. The changes are concentrated in three places:
- a one-step extension may pick its new point from *any* measure $U(\alpha)$ of the sequence, so the three-way split is made separately for each $\alpha$, and the shrunken measure-one set is a *union* $A^* = \bigcup_\alpha A(\alpha)$, which lies in $\bigcap \vec{V}$ but in general in no single $U(\alpha)$;
- a new entry need not be an ordinal: a pair $\langle \nu, \vec{F}_\nu \rangle$ enters the stem together with its own block, so a direct extension deciding $\sigma$ shrinks blocks as well, and these blocks must be synchronized over the measure in use — this is the role of the sets $A^{<\alpha}$ and $A'(\alpha)$ below;
- an extension may also insert points into the blocks of triples already present in the stem, so in the minimality argument the new entries of a $\neg\sigma$-extension can be scattered relative to the chosen measure; the sets $A^{\leq\alpha}$, $A^{>\alpha}$ and the final three-case analysis locate them.

The diagonal intersections themselves are the usual ones ([[Chapter 1 - Measure Sequences#^def-1-3-1|Definition 1.3.1]]), evaluated in $M$ using that $j$ fixes $V_\kappa$ pointwise.

>[!lemma] Lemma 2.4.4 (Gitik, Lemma 5.8; Prikry property).
>$\langle \mathbb{R}_{\vec{V}}, \leq, \leq^* \rangle$ satisfies the Prikry property: for every $p \in \mathbb{R}_{\vec{V}}$ and every statement $\sigma$ of the forcing language there is $p^* \leq^* p$ deciding $\sigma$.
> ^lem-2-4-4

*Proof.* We assume for simplicity that $p = \langle \langle \kappa, \vec{V} \rangle, A \rangle$; the general case is obtained by applying the same argument to each block of the stem, using [[#^lem-2-4-2|Lemma 2.4.2]]. Suppose, towards a contradiction, that no direct extension of $p$ decides $\sigma$.

**Preparation: one-step extensions.** For a finite sequence $\vec{d} = \langle d_1, \dots, d_n \rangle$ from $V_\kappa$, write
$$\vec{d}^\frown p = \langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \setminus V_{\kappa(d_n)+1} \rangle$$
whenever this is a condition. Let
$$\tilde{A}(\vec{d}) = \{d \in A \mid d \text{ an ordinal and } \vec{d}^\frown d^\frown p \in \mathbb{R}_{\vec{V}}, \text{ or } d = \langle \nu, \vec{F}_\nu \rangle \text{ and } \vec{d}^\frown \langle \nu, \vec{F}_\nu, A \cap V_\nu \rangle^\frown p \in \mathbb{R}_{\vec{V}}\}.$$
Then $\tilde{A}(\vec{d}) \in \bigcap \vec{V}$. Split $\tilde{A}(\vec{d})$ into three parts: $A_0(\vec{d})$ consists of those $d \in \tilde{A}(\vec{d})$ for which the corresponding one-step extension has a *direct* extension forcing $\sigma$, i.e.
- if $d$ is an ordinal: for some $B_d$, $\langle \vec{d}^\frown d, \langle \kappa, \vec{V} \rangle, B_d \rangle \leq^* \vec{d}^\frown d^\frown p$ and $\langle \vec{d}^\frown d, \langle \kappa, \vec{V} \rangle, B_d \rangle \Vdash \sigma$;
- if $d = \langle \nu, \vec{F}_\nu \rangle$: for some $B_d$ and $b_d$, $\langle \vec{d}^\frown \langle \nu, \vec{F}_\nu, b_d \rangle, \langle \kappa, \vec{V} \rangle, B_d \rangle \leq^* \vec{d}^\frown \langle \nu, \vec{F}_\nu, A \cap V_\nu \rangle^\frown p$ and it forces $\sigma$;

$A_1(\vec{d})$ is defined identically with $\neg \sigma$ in place of $\sigma$, and $A_2(\vec{d}) = \tilde{A}(\vec{d}) \setminus (A_0(\vec{d}) \cup A_1(\vec{d}))$. Note that $A_0(\vec{d}) \cap A_1(\vec{d}) = \emptyset$: two direct extensions of the same condition are compatible, so no $d$ can admit both.

For each $\alpha < \mathrm{length}(\vec{V})$ choose $i_\alpha \leq 2$ with $A_{i_\alpha}(\vec{d}) \in U(\alpha)$ and set $A(\alpha, \vec{d}) = A_{i_\alpha}(\vec{d})$; if $\vec{d}^\frown p \notin \mathbb{R}_{\vec{V}}$, set $A(\alpha, \vec{d}) = A$. Now take the diagonal intersection (in the sense of [[Chapter 1 - Measure Sequences#^def-1-3-1|Definition 1.3.1]])
$$A(\alpha) = \{d \in A \mid \forall \vec{d} \in [V_\kappa]^{<\omega}\ (\max\nolimits_k \kappa(d_k) < \kappa(d) \Rightarrow d \in A(\alpha, \vec{d}))\}.$$

**Claim 1.** $A(\alpha) \in U(\alpha)$.

*Proof.* For every $\vec{d} \in [V_\kappa]^{<\omega}$ we have $A(\alpha, \vec{d}) \in U(\alpha)$, i.e. $\langle \kappa, \vec{V} \upharpoonright \alpha \rangle \in j(A(\alpha, \vec{d}))$ in $M$. Since $V_\kappa^M = V_\kappa$, the finite sequences $\vec{d}$ quantified over in $j(A(\alpha))$ are exactly those of $V$; and $\kappa(\langle \kappa, \vec{V} \upharpoonright \alpha \rangle) = \kappa$ exceeds $\max_k \kappa(d_k)$ for every such $\vec{d}$. Hence $\langle \kappa, \vec{V} \upharpoonright \alpha \rangle \in j(A(\alpha))$, which means $A(\alpha) \in U(\alpha)$. $\dashv$

Set $A^* = \bigcup_{\alpha < \mathrm{length}(\vec{V})} A(\alpha)$. Then $A^* \supseteq A(\beta) \in U(\beta)$ for every $\beta$, so $A^* \in \bigcap \vec{V}$ by upward closure. Put $p^* = \langle \langle \kappa, \vec{V} \rangle, A^* \rangle \leq^* p$.

**Minimal length.** By our assumption, no direct extension of $p^*$ decides $\sigma$. Pick an extension $\langle d_1, \dots, d_{n+1}, \langle \kappa, \vec{V} \rangle, B \rangle \leq p^*$ deciding $\sigma$ with $n$ as small as possible; say it forces $\sigma$. Pick $\alpha < \mathrm{length}(\vec{V})$ with $d_{n+1} \in A(\alpha)$ and write $\vec{d} = \langle d_1, \dots, d_n \rangle$. The decider is a direct extension of $\vec{d}^\frown d_{n+1}^\frown p^*$ forcing $\sigma$, so $d_{n+1} \in A_0(\vec{d})$; in particular $i_\alpha = 0$ and $A(\alpha, \vec{d}) = A_0(\vec{d})$. Since $\kappa(d) > \kappa(d_n)$ implies $d \in A(\alpha, \vec{d})$ for every $d \in A(\alpha)$, we conclude:
$$(\star) \quad \text{for every } d \in A(\alpha) \setminus V_{\kappa(d_n)+1} \text{ there are } \tilde{d} \text{ and } B_d \text{ with } \langle \vec{d}^\frown \tilde{d}, \langle \kappa, \vec{V} \rangle, B_d \rangle \leq^* \vec{d}^\frown d^\frown p^* \text{ forcing } \sigma,$$
where $\tilde{d} = d$ if $d$ is an ordinal, and $\tilde{d} = \langle \nu, \vec{F}_\nu, b_d \rangle$ for some $b_d \in \bigcap \vec{F}_\nu$ if $d = \langle \nu, \vec{F}_\nu \rangle$.

We will find a set $C$ such that $\langle \vec{d}, \langle \kappa, \vec{V} \rangle, C \rangle \leq p^*$ forces $\sigma$, contradicting the minimality of $n$.

**Shrinking below $\alpha$.** Suppose $\alpha > 0$ (the case $\alpha = 0$ is similar and slightly easier). Take the diagonal intersection of the $B_d$'s:
$$B^* = \{e \in A^* \mid \forall d \in V_{\kappa(e)}\ (B_d \text{ is defined} \Rightarrow e \in B_d)\}.$$

**Claim 2.** $B^* \in U(\beta)$ for every $\beta < \mathrm{length}(\vec{V})$.

*Proof.* For each $d$ with $B_d$ defined, $B_d \in \bigcap \vec{V}$, so in $M$, $\langle \kappa, \vec{V} \upharpoonright \beta \rangle \in j(B_d)$. Since $V_\kappa^M = V_\kappa$, the quantification over $d \in V_{\kappa(\langle \kappa, \vec{V} \upharpoonright \beta \rangle)} = V_\kappa$ in $j(B^*)$ ranges exactly over the $d$'s of $V$. Hence $\langle \kappa, \vec{V} \upharpoonright \beta \rangle \in j(B^*)$. $\dashv$

Each $b_d$ lies in $\bigcap \vec{F}_\nu$ (it is the block of a legal condition). Consider
$$A^{<\alpha} = j(\langle b_d \mid d \in A(\alpha) \rangle)(\vec{V} \upharpoonright \alpha),$$
the value of the function $d \mapsto b_d$ at the generic point $\vec{V} \upharpoonright \alpha$; this is defined since $A(\alpha) \in U(\alpha)$. By elementarity, $A^{<\alpha} \in U(\beta)$ for every $\beta < \alpha$. Next, the set
$$A'(\alpha) = \{d \in A(\alpha) \mid A^{<\alpha} \cap V_{\kappa(d)} = b_d\}$$
lies in $U(\alpha)$: indeed $j(A^{<\alpha}) \cap V_\kappa = A^{<\alpha} = j(\langle b_d \mid d \in A(\alpha)\rangle)(\vec{V} \upharpoonright \alpha)$, so $\vec{V} \upharpoonright \alpha \in j(A'(\alpha))$. Set $A^{\leq \alpha} = (A^{<\alpha} \cup A'(\alpha)) \cap A^*$; then $A^{\leq \alpha} \in U(\beta)$ for every $\beta \leq \alpha$.

**Shrinking above $\alpha$.** Consider
$$A^{>\alpha} = \{\langle \nu, \vec{F} \rangle \in A^* \mid \exists \xi < \mathrm{length}(\vec{F})\ (A'(\alpha) \cap V_\nu \in F(\xi))\}.$$
Then $A^{>\alpha} \in U(\beta)$ for every $\beta$ with $\alpha < \beta < \mathrm{length}(\vec{V})$: in $M$, $j(A'(\alpha)) \cap V_\kappa = A'(\alpha) \in U(\alpha)$, so $\xi = \alpha < \beta$ witnesses $\langle \kappa, \vec{V} \upharpoonright \beta \rangle \in j(A^{>\alpha})$. Finally set
$$A^{**} = (A^{\leq \alpha} \cup A^{>\alpha}) \cap B^*.$$
Then $A^{**} \in \bigcap \vec{V}$: for $\beta \leq \alpha$ it contains $A^{\leq \alpha} \cap B^* \in U(\beta)$, and for $\beta > \alpha$ it contains $A^{>\alpha} \cap B^* \in U(\beta)$.

**Three cases.** Let $p^{**} = \langle \langle \kappa, \vec{V} \rangle, A^{**} \rangle$ and $q = \vec{d}^\frown p^{**}$. By the minimality of $n$, no direct extension of $q$ decides $\sigma$. Pick $r \leq q$ with $r \Vdash \neg \sigma$, say $r = \langle e_1, \dots, e_m, \langle \kappa, \vec{V} \rangle, C \rangle$. By [[#^def-2-2-2|Definition 2.2.2]](3) there is $k \leq m$ with $\kappa(d_n) = \kappa(e_k)$.

**Case 1: $k = m$.** Choose $d = \langle \nu, \vec{F}_\nu \rangle \in A(\alpha) \cap C$ with $\kappa(d) > \kappa(e_m)$ and $C \cap V_\nu \in \bigcap \vec{F}_\nu$ (possible: apply [[Chapter 1 - Measure Sequences#^ex-1-4-5|Lemma 1.4.5]] to $A(\alpha) \cap C \in U(\alpha)$). Since $d \in A(\alpha)$ and $d \in B^*$'s index set, $(\star)$ gives $b_d$ with
$$s = \langle d_1, \dots, d_n, \langle \langle \nu, \vec{F}_\nu \rangle, b_d \rangle, \langle \kappa, \vec{V} \rangle, A^{**} \setminus V_{\kappa(d)+1} \rangle \Vdash \sigma.$$
Then $t = \langle e_1, \dots, e_m, \langle \langle \nu, \vec{F}_\nu \rangle, b_d \cap C \rangle, \langle \kappa, \vec{V} \rangle, A^{**} \cap C \setminus V_{\kappa(d)+1} \rangle$ extends both $s$ (the block $b_d \cap C \subseteq b_d$, the tail set $\subseteq A^{**} \setminus V_{\kappa(d)+1}$) and $r$ (via $\langle \nu, \vec{F}_\nu \rangle \in C$, by clause (4a)). But $t$ extends a condition forcing $\sigma$ and a condition forcing $\neg \sigma$ — impossible.

**Case 2: $k < m$ and $e_j \in A^{<\alpha}$ for all $k < j \leq m$.** Pick $d = \langle \nu, \vec{F}_\nu \rangle \in A'(\alpha) \cap C$ with $\kappa(d) > \kappa(e_m)$ and $C \cap A^{<\alpha} \cap V_\nu \in \bigcap \vec{F}_\nu$ ([[Chapter 1 - Measure Sequences#^ex-1-4-5|Lemma 1.4.5]] again). Since $d \in A'(\alpha)$, we have $b_d = A^{<\alpha} \cap V_\nu$, so
$$s = \langle d_1, \dots, d_n, \langle \langle \nu, \vec{F}_\nu \rangle, A^{<\alpha} \cap V_\nu \rangle, \langle \kappa, \vec{V} \rangle, A^{**} \setminus V_{\kappa(d)+1} \rangle \Vdash \sigma.$$
Consider $t = \langle e_1, \dots, e_m, \langle \langle \nu, \vec{F}_\nu \rangle, C \cap A^{<\alpha} \cap V_\nu \rangle, \langle \kappa, \vec{V} \rangle, A^{**} \cap C \setminus V_{\kappa(d)+1} \rangle$. Then $t \leq s$: the entries $e_1, \dots, e_k$ correspond to $d_1, \dots, d_n$ (since $r \leq q$), and the entries $e_j$ with $k < j \leq m$ lie in $A^{<\alpha} \cap V_\nu = b_d$, hence are insertions into the block of $\langle \langle \nu, \vec{F}_\nu \rangle, A^{<\alpha} \cap V_\nu \rangle$ permitted by clause (4b). Also $t \leq r$ by clause (4a), since $\langle \nu, \vec{F}_\nu \rangle \in C$. Again this contradicts $r \Vdash \neg \sigma$.

**Case 3: $k < m$ and some $e_j \notin A^{<\alpha}$.** Let $j^*$ be the minimal such $j$. Since $e_{j^*} \in A^{**} \subseteq A^{\leq\alpha} \cup A^{>\alpha}$ and $e_{j^*} \notin A^{<\alpha}$, we have $e_{j^*} \in A'(\alpha) \cup A^{>\alpha}$.

*Subcase 3a: $e_{j^*} \in A'(\alpha)$.* Write $e_{j^*} = \langle \langle \nu, \vec{F}_\nu \rangle, E \rangle$. Then $b_{e_{j^*}} = A^{<\alpha} \cap V_\nu$, so
$$s = \langle d_1, \dots, d_n, \langle \langle \nu, \vec{F}_\nu \rangle, A^{<\alpha} \cap V_\nu \rangle, \langle \kappa, \vec{V} \rangle, A^{**} \setminus V_{\nu+1} \rangle \Vdash \sigma,$$
and $t = \langle e_1, \dots, e_{j^*-1}, \langle \langle \nu, \vec{F}_\nu \rangle, E \cap A^{<\alpha} \rangle, \langle \kappa, \vec{V} \rangle, A^{**} \setminus V_{\nu+1} \rangle \leq s$ by the minimality of $j^*$ (the entries $e_j$ with $k < j < j^*$ lie in $A^{<\alpha}$). But $t$ and $r$ are compatible: intersect the blocks and measure-one sets. This contradicts $r \Vdash \neg \sigma$.

*Subcase 3b: $\langle \nu, \vec{F}_\nu \rangle \in A^{>\alpha}$, where $e_{j^*} = \langle \langle \nu, \vec{F}_\nu \rangle, E \rangle$, $E \in \bigcap \vec{F}_\nu$.* By the definition of $A^{>\alpha}$, there is $\xi < \mathrm{length}(\vec{F}_\nu)$ with $A'(\alpha) \cap V_\nu \in F_\nu(\xi)$; hence $A'(\alpha) \cap E \in F_\nu(\xi)$. Since $\vec{F}_\nu \in \mathcal{A}$, [[Chapter 1 - Measure Sequences#^ex-1-4-5|Lemma 1.4.5]] provides $\langle \tau, \vec{G}_\tau \rangle \in (A'(\alpha) \cap E) \setminus V_{\kappa(e_{j^*-1})+1}$ with $E \cap V_\tau \in \bigcap \vec{G}_\tau$. Extend $r$ by inserting $\langle \langle \tau, \vec{G}_\tau \rangle, E \cap V_\tau \rangle$ into the block of $e_{j^*}$: the resulting $r' \leq r$ still forces $\neg \sigma$, but now the entry following $e_{j^*-1}$ comes from $A'(\alpha)$, and we are back in Subcase 3a. Contradiction.

All cases are impossible; hence some direct extension of $p$ decides $\sigma$ after all. $\blacksquare$

Combining the lemmas, we obtain the main preservation theorem.

>[!theorem] Theorem 2.4.5 (Gitik, Theorem 5.9).
>Let $G \subseteq \mathbb{R}_{\vec{V}}$ be generic. Then $V[G]$ is a cardinal-preserving extension of $V$.
> ^thm-2-4-5

*Proof.* By induction on $\kappa = \kappa(\vec{V})$. Fix $p \in \mathbb{R}_{\vec{V}}$ and a cardinal $\xi$; we show $\xi$ is preserved below $p$.

*Case $\xi > \kappa$.* By [[#^lem-2-4-1|Lemma 2.4.1]], $\mathbb{R}_{\vec{V}}$ has the $\kappa^+$-c.c., so all cardinals $\geq \kappa^+$ are preserved.

*Case $\xi \leq \kappa$.* Suppose the stem of $p$ contains a triple $d_m = \langle \nu_m, \vec{V}_m, A_m \rangle$ with $\nu_m < \xi$, and take the last such $m$. By [[#^lem-2-4-2|Lemma 2.4.2]],
$$\mathbb{R}_{\vec{V}}/p \simeq \mathbb{R}_{\vec{V}_m}/p^{\leq m} \times \mathbb{R}_{\vec{V}}/p^{>m}.$$
The first factor is a Radin forcing on $\nu_m < \kappa$ and preserves all cardinals by the induction hypothesis. In the second factor $\xi > \nu_m$, so we may argue with $\mathbb{R}_{\vec{V}}/p^{>m}$ in place of $\mathbb{R}_{\vec{V}}/p$. Hence we may assume that every triple in the stem of $p$ satisfies $\kappa(d_m) \geq \xi$; for simplicity of notation, assume the stem has no triples at all (the general case is identical, working above $\rho = \min\{\kappa(d_m) \mid d_m \text{ a triple}\} \geq \xi$).

It suffices to show that no new subsets of $\delta$ are added for any cardinal $\delta < \xi$: a collapse of $\xi$ to some $\delta < \xi$ would yield such a new subset (coding the collapsing well-order). So fix $\delta < \xi$ ($\delta < \kappa$) and shrink: $p^* = \langle \langle \kappa, \vec{V} \rangle, A \setminus V_{\delta+1} \rangle \leq^* p$. Every extension of $p^*$ has all its stem points above $\delta$, so by the completeness of the relevant filters, $\langle \mathbb{R}_{\vec{V}}/p^*, \leq^* \rangle$ is $\delta^+$-closed. Now let $\dot{\tau}$ be a name with $p^* \Vdash \dot{\tau} \subseteq \check{\delta}$. Using the Prikry property ([[#^lem-2-4-4|Lemma 2.4.4]]) successively and taking lower bounds by $\delta^+$-closure, we find a $\leq^*$-chain $\langle p_\gamma \mid \gamma \leq \delta \rangle$ with $p_0 = p^*$ and $p_{\gamma+1} \leq^* p_\gamma$ such that $p_{\gamma+1}$ decides $\dot{\tau}(\check{\gamma})$. Then $p_\delta$ forces $\dot{\tau}$ to equal a ground model subset of $\delta$. $\blacksquare$

---

## Notes

The definition of $\mathbb{R}_{\vec{V}}$ follows Gitik's Definitions 5.2–5.4, which in turn follow Woodin's concrete approach to the forcing originally isolated axiomatically by Radin [48] and Mitchell (see also Cummings–Woodin [10]); we have reversed Gitik's order convention, so that for us $p \leq q$ means that $p$ is stronger than $q$. Lemmas 2.4.1–2.4.3 and [[#^thm-2-4-5|Theorem 2.4.5]] are Gitik's Lemmas 5.5–5.7 and Theorem 5.9; [[#^lem-2-4-4|Lemma 2.4.4]] is Gitik's Lemma 5.8, whose proof is the technical heart of the subject. [[#^prop-2-3-1|Proposition 2.3.1]] makes precise Gitik's remark that the length-$1$ case "is the usual Prikry forcing"; the analysis of one-step extensions in Sections 2.1 and 2.3 is Gitik's treatment of the case $\alpha^* = 2$.


---

## References

Main reference:

- Moti Gitik. Prikry-type forcings. In Matthew Foreman and Akihiro Kanamori, editors, *Handbook of Set Theory*, pages 1351–1447. Springer, Dordrecht, 2010.

Numbering below follows the bibliography of Gitik's chapter:

- [10] James Cummings and W. Hugh Woodin. *A book on Radin forcing*. In preparation.
- [48] Lon B. Radin. Adding closed cofinal sequences to large cardinals. *Annals of Mathematical Logic*, 22(3):243–261, 1982.

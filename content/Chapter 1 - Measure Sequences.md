
Prikry forcing singularizes a measurable cardinal $\kappa$ using a single normal measure on $\kappa$. Radin forcing replaces this single measure by a long sequence of measures on $V_\kappa$, all derived from one elementary embedding. The generic object will then be a sequence of points of $V_\kappa$ — ordinals and smaller measure sequences — whose first coordinates form a closed unbounded subset of $\kappa$. In this chapter we develop the notion of a *measure sequence* and isolate the class $\mathcal{A}$ from which the forcing conditions will be drawn.

We follow the concrete approach due to Woodin, as presented in Gitik's chapter of the Handbook.

>[!note] Notation.
>Throughout these notes we follow the notation of Gitik, *Prikry-Type Forcings* (Handbook of Set Theory, Ch. 16, §5.1), which will be our default setting. We keep Cummings' terms *weak measure sequence* and *constructing embedding*, which Gitik uses only implicitly.

---

## 1.1 Measure sequences derived from an embedding

>[!definition] Definition 1.1.1
>Let $j : V \to M$ be an elementary embedding into a transitive inner model $M$ with $\mathrm{crit}(j) = \kappa$. Define a sequence $\vec{U}$ by recursion on $\alpha$:
>- $U(0) = \{X \subseteq V_\kappa \mid \kappa \in j(X)\}$, the normal ultrafilter over $V_\kappa$ derived from $j$; it concentrates on ordinals and is nothing but the usual derived normal measure on $\kappa$, viewed as a measure on $V_\kappa$;
>- if $\vec{U} \upharpoonright \alpha = \langle \kappa, U(\beta) \mid \beta < \alpha \rangle \in M$, then
>$$U(\alpha) = \{X \subseteq V_\kappa \mid \vec{U} \upharpoonright \alpha \in j(X)\};$$
>- the **length** $\mathrm{length}(\vec{U})$ is the least $\alpha$ such that $\vec{U} \upharpoonright \alpha \notin M$.
>
>We call $\vec{U} = \langle \kappa, U(\alpha) \mid \alpha < \mathrm{length}(\vec{U}) \rangle$ and its initial segments **$j$-sequences of ultrafilters**. Note that all the $U(\alpha)$ are ultrafilters on the same underlying set $V_\kappa$; this uniformity will be essential once measures from different levels of a sequence meet inside a single forcing condition.
> ^def-1-1-1

>[!exercise] Exercise 1.1.2
>Show that for every $\alpha < \mathrm{length}(\vec{U})$, $U(\alpha)$ is a $\kappa$-complete ultrafilter over $V_\kappa$ (for $\alpha = 0$ it concentrates on ordinals).
> ^ex-1-1-2

---

## 1.2 Weak measure sequences

For $\alpha \geq 1$ the measures $U(\alpha)$ do not concentrate on ordinals but on sequences resembling initial segments of $\vec{U}$ itself.

>[!definition] Definition 1.2.1
>A sequence $w = \langle \kappa(w) \rangle ^\frown \langle w(\alpha) \mid \alpha < \mathrm{length}(w) \rangle$ is a **weak measure sequence (wms)** iff
>- $\kappa(w)$ is an inaccessible cardinal;
>- every $w(\alpha)$ is a measure on $V_{\kappa(w)}$;
>- $w(0)$ is normal and concentrates on ordinals.
>
>We write $\kappa(w)$ for the first coordinate of $w$.
> ^def-1-2-1

Note: a weak measure sequence is, literally, merely a sequence of measures. The only constraints are that all of its measures live on the same underlying set $V_{\kappa(w)}$, and that $w(0)$ is normal and concentrates on ordinals.

>[!exercise] Exercise 1.2.2
>Show that for every $\alpha$ with $0 < \alpha < \mathrm{length}(\vec{U})$, $U(\alpha)$ concentrates on weak measure sequences, i.e.
>$$\{w \in V_\kappa \mid w \text{ is a wms}\} \in U(\alpha).$$
>In particular $U(1)$ concentrates on pairs $\langle \nu, F \rangle$ with $\nu$ measurable below $\kappa$ and $F$ a normal ultrafilter over $V_\nu$.
>(Hint: work in $M$ and check that $\vec{U} \upharpoonright \alpha$ is itself a wms.)
> ^ex-1-2-2

---

## 1.3 Normality

The measures $U(\alpha)$ are *normal* in the following sense, which is the form of diagonal intersection appropriate for sequences rather than ordinals.

>[!definition] Definition 1.3.1
>Let $\langle A_x \mid x \in V_\kappa \rangle$ be a family of sets of weak measure sequences. Their **diagonal intersection** is
>$$\Delta_{x \in V_\kappa} A_x = \{w \mid \forall x \in V_{\kappa(w)}\ (w \in A_x)\}.$$
> ^def-1-3-1

>[!exercise] Exercise 1.3.2 (Normality).
>If $A_x \in U(\alpha)$ for every $x \in V_\kappa$, then $\Delta_{x \in V_\kappa} A_x \in U(\alpha)$.
>(Hint: show $\vec{U} \upharpoonright \alpha \in j(\Delta_x A_x)$, using that $j$ fixes $V_\kappa$ pointwise.)
> ^ex-1-3-2

---

## 1.4 The hierarchy $\mathcal{A}$

>[!definition] Definition 1.4.1
>A weak measure sequence $\vec{F}$ is a **measure sequence** if it is a $j$-sequence of ultrafilters for some embedding $j$ with $\mathrm{crit}(j) = \kappa(\vec{F})$; such a $j$ is called a **constructing embedding** for $\vec{F}$.
> ^def-1-4-1

Not every measure sequence is suitable as a building block for the forcing: we want sequences whose measures concentrate on sequences of the same kind. This is achieved by the following hierarchy.

>[!definition] Definition 1.4.2
>Define by recursion on $n < \omega$:
>- $A^{(0)} = \{\vec{F} \mid \vec{F} \text{ is a } j\text{-sequence of ultrafilters for some } j : V \to M\}$;
>- $A^{(n+1)} = \{\vec{F} \in A^{(n)} \mid \forall \alpha\ (0 < \alpha < \mathrm{length}(\vec{F}) \Rightarrow A^{(n)} \cap V_{\kappa(\vec{F})} \in F(\alpha))\}$;
>- $\mathcal{A} = \bigcap_{n<\omega} A^{(n)}$.
> ^def-1-4-2

>[!exercise] Exercise 1.4.3
>Show that if $\vec{F} \in \mathcal{A}$, then every measure on $\vec{F}$ concentrates on $\mathcal{A}$, i.e. $\mathcal{A} \cap V_{\kappa(\vec{F})} \in F(\alpha)$ for all $0 < \alpha < \mathrm{length}(\vec{F})$. (Use countable completeness of the measures.)
> ^ex-1-4-3

>[!definition] Definition 1.4.4
>For a sequence $\vec{F} = \langle \kappa(\vec{F}), F(0), F(1), \dots \rangle$, let
>$$\textstyle\bigcap \vec{F} = \bigcap \{F(\tau) \mid \tau < \mathrm{length}(\vec{F})\}.$$
>If $\mathrm{length}(\vec{F}) = 0$, i.e. $\vec{F} = \langle \kappa(\vec{F}) \rangle$, we set $\bigcap \vec{F} = \{\emptyset\}$ by convention. 
> ^def-1-4-4

>[!exercise] Exercise 1.4.5
>Show that $\bigcap \vec{F}$ is a $\kappa(\vec{F})$-complete filter whenever $\mathrm{length}(\vec{F}) \geq 1$.
> ^ex-1-4-5

The next lemma is what will make one-step extensions of the Radin forcing legitimate: if $w \in A$ and $A \cap V_{\kappa(w)} \in \bigcap w$, then $w$ is *addable* to $(\vec{F}, A)$.

>[!lemma] Lemma 1.4.6
>Let $\vec{F} \in \mathcal{A}$ and $A \in \bigcap \vec{F}$. Then $$B = \{w \in A \mid w \text{ is an ordinal, or } \mathrm{length}(w) \geq 1 \text{ and } A \cap V_{\kappa(w)} \in \textstyle\bigcap w\} \in \bigcap \vec{F}.$$
> ^lem-1-4-6

*Proof.* Let $j$ be a constructing embedding for $\vec{F}$ and fix $\alpha < \mathrm{length}(\vec{F})$; we show $B \in F(\alpha)$. For $\alpha = 0$: $F(0)$ concentrates on ordinals, every ordinal passes the defining condition of $B$ vacuously, and $\kappa \in j(A)$ since $A \in F(0)$; hence $\kappa \in j(B)$, i.e. $B \in F(0)$.

Now let $\alpha \geq 1$; we show $\vec{F} \upharpoonright \alpha \in j(B)$. By elementarity, $j(B)$ is computed in $M$ by the same formula, so we need:
1. $\vec{F} \upharpoonright \alpha \in j(A)$: this is exactly $A \in F(\alpha)$.
2. $j(A) \cap V_\kappa \in \bigcap (\vec{F} \upharpoonright \alpha) = \bigcap_{\beta < \alpha} F(\beta)$: since $j$ fixes $V_\kappa$ pointwise, $j(A) \cap V_\kappa \supseteq j``A = A$, and $A \in F(\beta)$ for every $\beta < \alpha$; by upward closure $j(A) \cap V_\kappa \in F(\beta)$ for all such $\beta$.

Hence $\vec{F} \upharpoonright \alpha \in j(B)$, as required. $\blacksquare$

---

## 1.5 Long measure sequences

Radin forcing with a sequence of length $\delta$ will change the cofinality of $\kappa$ to $\mathrm{cf}(\delta)$, so applications require long measure sequences in $\mathcal{A}$. The following lemma of Cummings and Woodin shows that a moderately strong embedding already provides sequences of length $(2^\kappa)^+$.

>[!lemma] Lemma 1.5.1 (Gitik, Lemma 5.1).
>Let $E$ be a $(\kappa, \lambda)$-extender and $j : V \to M \simeq Ult(V, E)$ the corresponding elementary embedding, so that $M \supseteq V_{\kappa+2}$ and ${}^\kappa M \subseteq M$. Let $\vec{U}$ be the $j$-sequence of ultrafilters of the maximal length. Then
>(a) $\mathrm{length}(\vec{U}) \geq (2^\kappa)^+$;
>(b) for every $\alpha < (2^\kappa)^+$, $\vec{U} \upharpoonright \alpha \in \mathcal{A}$.
> ^lem-1-5-1

*Proof.* **(a)** We claim ${}^\alpha V_{\kappa+2} \subseteq M$ for every $\alpha < (2^\kappa)^+$. Given $f : \alpha \to V_{\kappa+2}$, work in $M$: since $V_{\kappa+2} \subseteq M$, $M$ computes $V_{\kappa+2}$ and $2^\kappa$ correctly, so there is a bijection $\pi : 2^\kappa \to V_{\kappa+2}$ in $M$. Then $h = \pi^{-1} \circ f : \alpha \to 2^\kappa$ is (coded by) a subset of $2^\kappa$, hence $h \in V_{\kappa+2} \subseteq M$, and $f = \pi \circ h \in M$. Since each $U(\beta) \in V_{\kappa+2}$, the sequence $\vec{U} \upharpoonright \alpha$ is (coded by) an element of ${}^\alpha V_{\kappa+2} \subseteq M$. Thus the recursion defining $\vec{U}$ does not break down before $(2^\kappa)^+$.

**(b)** We show $\vec{U} \upharpoonright \alpha \in A^{(n)}$ for all $n < \omega$ and all $\alpha < (2^\kappa)^+$.

**Step 1: $\vec{U} \upharpoonright \alpha \in A^{(1)}$.** We must show that $A^{(0)} \cap V_\kappa \in U(\beta)$ for every $\beta$ with $0 < \beta < (2^\kappa)^+$. By the definition of $U(\beta)$ this means: in $M$, $\vec{U} \upharpoonright \beta \in j(A^{(0)})$, i.e. $M$ contains an embedding constructing $\vec{U} \upharpoonright \beta$.

Fix $\beta$ with $0 < \beta < (2^\kappa)^+$. We choose the truncation of $E$ according to the size of $\beta$:

- **Case 1:** $\beta > \kappa$. Let $E' = E \upharpoonright [\beta]^{<\omega}$.
- **Case 2:** $\beta \leq \kappa$. The truncation $E \upharpoonright [\beta]^{<\omega}$ is now *trivial*: since $j$ fixes every $a \in [\beta]^{<\omega}$, each of its measures is principal, so $Ult(V, E \upharpoonright [\beta]^{<\omega}) = V$ and the associated embedding is the identity — which cannot be a constructing embedding for anything. We therefore truncate further out and set $E' = E \upharpoonright [\kappa + \beta]^{<\omega}$.

In both cases $E'$ is nontrivial: its fragment at $\{\kappa\}$ is exactly $U(0)$ (this is precisely why Case 2 requires the longer truncation). Moreover $E'$ is coded by a $(\kappa + \beta)$-sequence of elements of $V_{\kappa+2}$, and $\kappa + \beta < (2^\kappa)^+$, so part (a) gives $E' \in M$. Let $j' : V \to M' \simeq Ult(V, E')$, let $k : M' \to M$ be the factor map with $j = k \circ j'$, and let $i = j' \upharpoonright M : M \to N$, where $N = j'(M) \simeq Ult(M, E')$ (the identification uses ${}^\kappa M \subseteq M$). Note that $\mathrm{crit}(i) = \kappa$, so $i$ is a legitimate candidate for a constructing embedding.

![](static/tikz/tikz-21ca756000.svg)

We record the standard properties of the factor map: $k \upharpoonright \beta = \mathrm{id}$ and $\mathrm{crit}(k) \geq \kappa^+$ (note $(\kappa^+)^{M'} = \kappa^+$ since $V_{\kappa+1} \subseteq M'$). In particular $k(\kappa) = \kappa$.

**Claim.** $k(U) = U$ for every measure $U$ on $V_\kappa$.

*Proof of Claim.* Since $\mathrm{crit}(k) > \kappa$, $k$ fixes $V_\kappa$ pointwise, so $U = k[U ]\subseteq k(U)$. Both are ultrafilters on $V_\kappa$, and $V_{\kappa+1} \cap M' = V_{\kappa+1} \cap M = V_{\kappa+1}$, so by maximality of $U$ as a filter, $U = k(U)$. $\dashv$

Now let $\vec{U}^*$ be the $i$-sequence of ultrafilters constructed in $M$. We show by induction on $\gamma < \beta$ that $U^*(\gamma) = U(\gamma)$. Suppose $\vec{U}^* \upharpoonright \gamma = \vec{U} \upharpoonright \gamma$. For $X \subseteq V_\kappa$ (note $X \in M$):

$$
\begin{aligned}
X \in U^*(\gamma) &\iff \vec{U}^* \upharpoonright \gamma \in i(X) \\
&\iff \vec{U} \upharpoonright \gamma \in j'(X) && (i = j' \upharpoonright M) \\
&\iff k(\vec{U} \upharpoonright \gamma) \in j(X) && (\text{elementarity of } k,\ j = k \circ j') \\
&\iff \vec{U} \upharpoonright \gamma \in j(X) && (k \text{ fixes } \kappa,\ \gamma,\ \text{and each } U(\delta) \text{ by the Claim}) \\
&\iff X \in U(\gamma).
\end{aligned}
$$

Hence in $M$, $\vec{U} \upharpoonright \beta$ is the $i$-sequence, so $\vec{U} \upharpoonright \beta \in j(A^{(0)})$, as required.

**Step 2: a general observation.** The following agreement holds for *any* elementary embedding $j : V \to M$ with $\mathrm{crit}(j) = \kappa$ — no closure hypothesis on $M$ is needed:
$$j(A^{(0)}) \cap V_\kappa = A^{(0)} \cap V_\kappa.$$
Indeed, $\mathrm{crit}(j) = \kappa$ gives $V_\kappa^M = V_\kappa$. For $\vec{F} \in V_\kappa$ we have the chain of equivalences
$$\vec{F} \in A^{(0)} \iff \text{some extender } E' \in V_\kappa \text{ constructs } \vec{F} \iff \vec{F} \in j(A^{(0)}).$$
For the first equivalence: given any constructing embedding $i'$ for $\vec{F}$ — with $\mathrm{crit}(i') = \kappa(\vec{F}) = \nu < \kappa$ and $\mathrm{length}(\vec{F}) < \kappa$ — the $(\nu, \mathrm{length}(\vec{F}) + 1)$-extender derived from $i'$ lies in $V_\kappa$ (since $\kappa$ is inaccessible) and constructs the same sequence; the converse is trivial. For the second equivalence: the assertion "$E' \in V_\kappa$ constructs $\vec{F}$" is absolute between $V$ and $M$, since it unfolds into a recursion of length $< \kappa$ whose parameters and intermediate objects all lie in $V_\kappa = H_\kappa$, which $V$ and $M$ compute identically.

*Remark.* This agreement is a general fact about embeddings with critical point $\kappa$, not a feature of the particular embedding at hand. Gitik's own wording at this point is somewhat misleading: he argues from the specifics of his $j$, and his appeal to "the same argument" for the iterates $j_{0,n-1}$ is only justified once the general observation is isolated — every $j_{0,n-1}$ has critical point $\kappa$, so Step 2 applies to each of them verbatim.

**Step 3: $\vec{U} \upharpoonright \alpha \in A^{(n)}$ for $n \geq 2$.** Inductively, $\vec{U} \upharpoonright \alpha \in A^{(n+1)}$ iff for all $\beta < \alpha$, $A^{(n)} \cap V_\kappa \in U(\beta)$, iff for all $\beta < \alpha$, $\vec{U} \upharpoonright \beta \in j(A^{(n)})$. Unwinding once more, this reduces to the agreement $j(A^{(0)}) \cap V_\kappa = A^{(0)} \cap V_\kappa$ of Step 2 together with Step 1. For larger $n$ the same argument is applied with $j$ replaced by the iterated ultrapower embedding $j_{0,n-1} : V \to M_{n-1}$ of $V$ by $E$; since $\mathrm{crit}(j_{0,n-1}) = \kappa$, Step 2 yields $j_{0,n-1}(A^{(0)}) \cap V_\kappa = A^{(0)} \cap V_\kappa$ directly. $\blacksquare$

*Remark.* Using stronger embeddings $j$ it is possible to show that much longer ultrafilter sequences belong to $\mathcal{A}$. For the basic theory of Radin forcing, length $(2^\kappa)^+$ is more than sufficient.

---

## 1.6 Mitchell order 2 is not enough: μ-measurability

Before moving on, let us see what the construction of Section 1.1 produces in the simplest nontrivial large cardinal situation, and isolate exactly the hypothesis needed to go further.

Suppose $o(\kappa) = 2$, and let $U_0 \lhd U_1$ be normal measures on $\kappa$ witnessing this: $U_0 \in M_1 = Ult(V, U_1)$, and no normal measure on $\kappa$ has Mitchell order $\geq 2$. By fixing a wellordering $f:\kappa\to V_\kappa$, we may redefine both $U_0$ and $U_1$ as normal measures over $V_\kappa$.  Let $j = j_{U_1} : V \to M_1$ be the ultrapower embedding, and let $\vec{U}$ be the $j$-sequence of ultrafilters of [[#^def-1-1-1|Definition 1.1.1]].

>[!example] Example 1.6.1 (The $j_{U_1}$-sequence).
>(a) $U(0) = U_1$: by definition, $X \in U(0) \iff \kappa \in j_{U_1}(X) \iff X \in U_1$.
>(b) $\mathrm{length}(\vec{U}) = 1$: to continue the recursion at $\alpha = 1$ we would need $\vec{U} \upharpoonright 1 = \langle \kappa, U_1 \rangle \in M_1$. But $U_1 \notin M_1$ by the standard fact that $U \notin Ult(V, U)$ for every normal measure $U$ (otherwise $U \lhd U$, contradicting the well-foundedness of the Mitchell order). Hence the recursion breaks down immediately, and the maximal $j_{U_1}$-sequence is just $\langle \kappa, U_1 \rangle$.
>(c) Consequently, Radin forcing with $\vec{V} = \langle \kappa, U_1 \rangle$ will be nothing but Prikry forcing with $U_1$ (the case $\alpha^* = 1$ of the next chapter).
>(d) $\langle \kappa, U_1 \rangle \in \mathcal{A}$: it belongs to $A^{(0)}$ by construction, and since $\mathrm{length}(\langle \kappa, U_1 \rangle) = 1$, the requirement "$A^{(n)} \cap V_{\kappa} \in F(\alpha)$ for all $0 < \alpha < \mathrm{length}(\vec{F})$" in [[#^def-1-4-2|Definition 1.4.2]] is vacuous. Hence $\langle \kappa, U_1 \rangle \in A^{(n)}$ for every $n$, and so $\langle \kappa, U_1 \rangle \in \mathcal{A}$. This is Gitik's remark that *every measurable cardinal is in $\mathcal{A}$*.
> ^exmp-1-6-1

**What $U_1$ concentrates on.** Although its own derived sequence is short, $U_1$ does "see" measure sequences below $\kappa$: since $U_0 \in M_1$ and ${}^\kappa M_1 \subseteq M_1$, $M_1 \models$ "$\kappa$ is measurable", so by Łoś
$$\{\nu < \kappa \mid \nu \text{ is measurable}\} \in U_1,$$
and each such $\nu$ is the first coordinate of a measure sequence $\langle \nu, F \rangle \in A^{(0)}$. This is the shadow of the case $\alpha^* = 2$: were there a next measure $U(1)$, it would concentrate on pairs $\langle \nu, F \rangle$ with $F$ a normal measure on $V_\nu$ (cf. [[#^ex-1-2-2|Exercise 1.2.2]]).

**The exact obstruction.** The obstruction in (b) is general: for $j = j_U$ the derived normal measure is $U$ itself, and $U \notin Ult(V, U)$, so the ultrapower by a single normal measure always yields a sequence of length $1$. Looking at the recursion of [[#^def-1-1-1|Definition 1.1.1]], continuation past $\alpha = 1$ requires exactly one thing:
$$\vec{U} \upharpoonright 1 = \langle \kappa, U(0) \rangle \in M \iff U(0) \in M,$$
i.e. the embedding must "re-absorb" its own derived normal measure. This property has a name.

>[!definition] Definition 1.6.3.
>A cardinal $\kappa$ is **μ-measurable** if there is an elementary embedding $j : V \to M$ with $\mathrm{crit}(j) = \kappa$ such that the derived normal measure $U = \{X \subseteq V_\kappa \mid \kappa \in j(X)\}$ belongs to $M$.
> ^def-1-6-3

Equivalently, $\kappa$ is μ-measurable iff there is an embedding whose derived sequence of ultrafilters has length $\geq 2$. Thus μ-measurability is exactly the hypothesis needed for a nontrivial Radin forcing: with $\vec{V} = \langle \kappa, U(0), U(1) \rangle$ the forcing already produces generic sequences of type $\omega^2$ (the case $\alpha^* = 2$ of the next chapter).

Several comments are in order.

**μ-measurability requires genuine extenders.** No ultrapower by a normal measure can witness μ-measurability, since $U \notin Ult(V, U)$; a witnessing embedding must therefore come from an extender which is not equivalent to a normal ultrafilter. In fact, μ-measurability is the *weakest* large cardinal property which requires the existence of extenders which are not equivalent to normal ultrafilters: its defining clause "$U(0) \in M$" is the minimal closure requirement beyond a plain ultrapower — the first rung at which the recursion of [[#^def-1-1-1|Definition 1.1.1]] produces anything beyond a normal measure.

**μ-measurable implies $o(\kappa) \geq 2$.** If $j$ witnesses μ-measurability, then $U \in M$, and one checks that $M \models$ "$U$ is a normal measure on $V_\kappa$" (every $X \in P(V_\kappa)^M$ is split by $U$, and $\kappa$-completeness and normality are computed using objects that remain in $M$). Hence $M \models$ "$\kappa$ is measurable", which by the definition of $U$ means
$$\{\nu < \kappa \mid \nu \text{ is measurable}\} \in U,$$
so $o(U) \geq 1$ and $o(\kappa) \geq 2$. The hypothesis of [[#^exmp-1-6-1|Example 1.6.1]] is therefore strictly weaker than μ-measurability.

**Consistency strength.** We state without proof that the consistency strength of a μ-measurable cardinal lies strictly between that of a measurable cardinal and that of a $(\kappa+2)$-strong cardinal:
$$\text{measurable} \;<\; \text{μ-measurable} \;<\; (\kappa+2)\text{-strong}.$$
The upper bound is immediate: if $j : V \to M$ witnesses that $\kappa$ is $(\kappa+2)$-strong, then $V_{\kappa+2} \subseteq M$, hence $U(0) \in V_{\kappa+2} \subseteq M$. This is precisely the hypothesis of [[#^lem-1-5-1|Lemma 1.5.1]], which therefore produces sequences of length $(2^\kappa)^+$ — far more than the length $2$ that μ-measurability barely provides.

>[!exercise] Exercise 1.6.2.
>Show that $\langle \kappa, U_1 \rangle \notin j_{U_1}(A^{(0)})$, i.e. $M_1$ does not believe that $\langle \kappa, U_1 \rangle$ is a measure sequence. (Hint: a constructing embedding for it inside $M_1$ would in particular yield $U_1 \in M_1$.) Conclude once more that the recursion of [[#^def-1-1-1|Definition 1.1.1]] stops at $\alpha = 1$.
> ^ex-1-6-2

>[!exercise] Exercise 1.6.4.
>Let $j : V \to M$ witness that $\kappa$ is μ-measurable, and let $U(1)$ be the second measure of the derived sequence. Show that $U(1)$ concentrates on pairs $\langle \nu, F \rangle$ with $\nu$ measurable and $F$ a normal measure on $V_\nu$. (Hint: in $M$, $\langle \kappa, U(0) \rangle$ is such a pair.)
> ^ex-1-6-4

---

## Notes

The forcing was originally defined axiomatically by Radin [48] and Mitchell, abstracting the properties a sequence of measures must satisfy; the concrete construction from a single embedding used here is due to Woodin. [[#^lem-1-5-1|Lemma 1.5.1]] is Lemma 5.1 of Gitik's chapter, where it is credited to Cummings–Woodin [10]. The class $\mathcal{A}$ will reappear as the reservoir from which all measure-one sets in the Radin forcing are taken: in Definition 5.2 of Gitik's chapter, conditions have the form $\langle d_1, \dots, d_n, \langle \kappa, \vec{V} \rangle, A \rangle$ with $A \in \bigcap \vec{V}$ and $A \subseteq \mathcal{A}$.


---

## References

Main reference:

- Moti Gitik. Prikry-type forcings. In Matthew Foreman and Akihiro Kanamori, editors, *Handbook of Set Theory*, pages 1351–1447. Springer, Dordrecht, 2010.

Numbering below follows the bibliography of Gitik's chapter:

- [10] James Cummings and W. Hugh Woodin. *A book on Radin forcing*. In preparation.
- [48] Lon B. Radin. Adding closed cofinal sequences to large cardinals. *Annals of Mathematical Logic*, 22(3):243–261, 1982.

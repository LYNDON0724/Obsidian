
# Lecture 1 — Radin Forcing: An Overview

> [!info] Source
> - **Speaker:** James Cummings
> - **Series:** Simons Semester "Gödel's Program", Banach Center, Warsaw (31.05.2026 – 05.07.2026); "Long Games and Chang Models" workshop led by Hugh Woodin, 8–12 June 2026
> - **Video:** *Radin Forcing (Lecture 1)*, Banach Center (YouTube), 1h 06m
> - **URL:** https://www.youtube.com/watch?v=GfK-_x94uXs
> - **Note:** These notes are reconstructed from an automatic transcript of the lecture, cross-checked against the terminology of [[Chapter 1 - Measure Sequences]] and [[Chapter 2 - The Radin Forcing]]. Where the transcript garbles symbols, the definitions below follow Gitik (Handbook of Set Theory, Ch. 16 §5) and Woodin's concrete approach. The lecture is a *three-hour* course; this is the first hour.

---

## 1. The plan and provenance

- Nothing in the course is original to the speaker; attributions are given along the way (Radin, Gitik, Woodin, Cummings–Woodin, Magidor).
- The course spends most time on the **original Radin forcing**, then discusses a variation: **supercompact Radin forcing**.
- The slogan: **Radin forcing is a generalization of Prikry forcing**. The audience is assumed to know Prikry forcing; if not, "Prikry forcing is just Radin forcing with a single measure".

### 1.1 What Prikry forcing already gives us (recap)

A few facts about Prikry forcing are assumed and will generalize:

1. **Parameter:** a single normal measure $U$ on $\kappa$.
2. It **preserves cardinals**; it adds a cofinal $\omega$-sequence in $\kappa$, so $\mathrm{cf}(\kappa) = \omega$.
3. **Prikry property:** every statement $\sigma$ of the forcing language is decided by *shrinking a measure-one set* (a direct extension).
4. A Prikry condition carries **two kinds of data**: finite information about the generic sequence chosen so far, plus constraints (a measure-one set) on what may be chosen later.
5. **Generic criterion (Prikry-genericity):** an $\omega$-sequence cofinal in $\kappa$ is generic iff it **diagonalizes** the normal measure. An appropriate analogue will hold for Radin forcing.
6. **Generics by iteration:** iterating a normal measure $\omega$ times and taking the critical sequence of the iteration yields a Prikry generic sequence. For Radin forcing one must **iterate much longer** — the Radin generic object is a more complex object.

> [!note] Key contrast to keep in mind
> Prikry forcing has **one measure, one measure-one set**. Radin forcing will have **many measure-one sets living on different objects**.

---

## 2. The parameter: generating a measure sequence from one embedding

Whereas Prikry forcing is defined from a single normal measure on $\kappa$, Radin forcing is defined from a **sequence of measures** on $V_\kappa$, generated from a **fixed elementary embedding**

$$j : V \to M, \qquad \operatorname{crit}(j) = \kappa.$$

- $j$ will witness some modest large cardinal property of $\kappa$ — some degree of *strength* or *supercompactness*.
- With a view to variations: there is an industry where one starts not with a fixed $j$ but with a coherent sequence of extenders; here $j$ is fixed initially, then becomes a *variable* (every measure sequence that appears in the forcing will carry its **own constructing embedding**).

### 2.1 The recursion defining the sequence

The first entry of the sequence is **not** a measure: it is the critical point $\kappa$. Then, as long as it makes sense, the sequence so far is used as a **seed** from which the next measure is derived:

- $U_J(0) = \{ X \subseteq V_\kappa \mid \kappa \in j(X) \}$ — the normal ultrafilter derived from $j$;
- given $\vec{U} \upharpoonright \alpha = \langle \kappa, U_J(\beta) \mid \beta < \alpha \rangle \in M$,
  $$U_J(\alpha) = \{ X \subseteq V_\kappa \mid \vec{U} \upharpoonright \alpha \in j(X) \};$$
- the **length** $\mathrm{length}(\vec{U})$ is the least $\alpha$ such that $\vec{U} \upharpoonright \alpha \notin M$.

(This is exactly Definition 1.1.1 of [[Chapter 1 - Measure Sequences#^def-1-1-1]].)

### 2.2 Small values of $\alpha$: self-similarity

The definition is heavily **self-similar**: each $U_J(\alpha)$ concentrates on objects that look like initial segments of $\vec{U}$ itself.

- **$\alpha = 1$:** technically $U_J(1)$ is not literally the derived normal measure; it concentrates on sequences with a single entry — it is "the normal measure in a transparent disguise".
- **$\alpha = 2$:** $U_J(2)$ is generated from the pair $\langle \kappa, U_J(1) \rangle$, and concentrates on pairs $\langle \nu, F \rangle$ where $\nu$ is inaccessible and $F$ is (morally) a measure on $V_\nu$.
- **$\alpha = 3$:** the generating object is $\langle \kappa, U_J(1), U_J(2) \rangle$, and $U_J(3)$ concentrates on triples: an inaccessible $\nu$, a measure on $V_\nu$, and a measure on a set consisting of inaccessibles-with-measures.

For $\gamma < \kappa$, $U_J(\gamma)$ concentrates on some family of sequences of length $\gamma$ — an inaccessible plus a sequence of measures below it — i.e. on **describable sets**. But:

> [!warning] The limit of describability
> By the time $\alpha$ reaches $\kappa^+$, one is "pretty much done" with the idea of describable sets on which the measures concentrate. Beyond that the picture becomes more confusing — and that is *good*, because one reaches the class of **repeat points**: stages in the construction at which "you have seen everything".

- **Repeat points** are a significant technical stage (used later, e.g. for singularizing to uncountable cofinalities).
- The value $2^{\kappa^+}$ will appear as a significant cardinal in the numerology later.

### 2.3 How much strength is needed?

- If $\kappa$ is the least measurable cardinal, the construction does not get far: $U_J(1)$ is already a measure, so it cannot be a member of $M$ in the right way; $\vec{U} \upharpoonright 2 \notin M$.
- Some **modest strength** suffices: if $j$ witnesses that $\kappa$ is $(\kappa+1)$-strong, then measures and sequences can be coded as elements of $V_{\kappa+2}$, and the recursion runs **quite a while**.
- In particular, with a little strength one can generate enough measures for something interesting to happen, and $2^{\kappa^+}$ is the natural bound (cf. Lemma 1.5.1: a $(\kappa,\lambda)$-extender gives $\mathrm{length}(\vec{U}) \geq (2^\kappa)^+$).

---

## 3. Weak measure sequences and normality

### 3.1 Weak measure sequences

The lecture introduces (as the "minimum" notion) what [[Chapter 1 - Measure Sequences#^def-1-2-1]] calls a **weak measure sequence** (wms):

> $w = \langle \kappa(w) \rangle ^\frown \langle w(\alpha) \mid \alpha < \mathrm{length}(w) \rangle$ is a **weak measure sequence** iff
> - $\kappa(w)$ is inaccessible;
> - each $w(\alpha)$ is a measure on $V_{\kappa(w)}$;
> - $w(0)$ is normal and concentrates on ordinals.

The $U_J(\alpha)$'s concentrate on wms's (Exercise 1.2.2). But for the forcing one will want **more stringent conditions** — see §5.

### 3.2 Normality and diagonal intersections

Normality plays a central role (the speaker emphasizes normality "in a slightly stronger sense" as the right tool, rather than e.g. Rowbottom-type theorems).

For a fixed $\alpha$ with $U_J(\alpha)$ defined, and a family $\langle A_x \mid x \in V_\kappa \rangle$ of sets of wms's, the **diagonal intersection** is

$$\Delta_{x \in V_\kappa} A_x = \{ w \in V_\kappa \mid \forall x \in V_{\kappa(w)}\ (w \in A_x) \},$$

exactly [[Chapter 1 - Measure Sequences#^def-1-3-1]].

**Normality:** if $A_x \in U_J(\alpha)$ for all $x \in V_\kappa$, then $\Delta_x A_x \in U_J(\alpha)$.

*Sketch of the verification (go to the $j$-side).* $U_J(\alpha)$ is generated by $\vec{U} \upharpoonright \alpha$, so it suffices to check $\vec{U} \upharpoonright \alpha \in j(\Delta_x A_x)$. The indices to worry about in $j(\Delta_x A_x)$ below $\kappa$ are exactly those in $V_\kappa$, which $j$ fixes pointwise; each such $x$ has $A_x \in U_J(\alpha)$, i.e. $\vec{U} \upharpoonright \alpha \in j(A_x)$. $\blacksquare$

### 3.3 The intersection filter

For a sequence $w$ with at least one measure, the natural filter is

$$\textstyle\bigcap w = \bigcap \{ w(\tau) \mid \tau < \mathrm{length}(w) \},$$

the intersection of all measures appearing on $w$ ([[Chapter 1 - Measure Sequences#^def-1-4-4]]). Since each $w(\tau)$ is a $\kappa(w)$-complete measure, $\bigcap w$ is a $\kappa(w)$-complete filter (Exercise 1.4.5). Moreover:

> Because each individual measure is normal, the intersection filter enjoys a "verbally identical" normality — closure under the same diagonal intersections, inherited componentwise.

---

## 4. Constructing embeddings and the hierarchy $\mathcal{A}$

### 4.1 Constructing embeddings

- Every measure sequence generated by an embedding is a **measure sequence** in the sense of [[Chapter 1 - Measure Sequences#^def-1-4-1]]: a wms $\vec{F}$ such that for some embedding $j$ with $\operatorname{crit}(j) = \kappa(\vec{F})$, each $F(\alpha) = \{ X \mid \vec{F} \upharpoonright \alpha \in j(X) \}$. Such a $j$ is a **constructing embedding** for $\vec{F}$.
- The lecture makes a **technical convenience** out of this: *every measure sequence appearing in the forcing is assumed to have a constructing embedding*.
  - Radin's original paper did *not* do this — it wrote down in a first-order way the "pleasant properties" such sequences have.
  - There is a natural candidate construction: given a measure, take its **ultrapower** as a constructing embedding; this works for some sequences, not all.
- One can ask whether a wms with **no two identical measures** has a canonical constructing embedding; the speaker leaves this as an open-ended remark.

### 4.2 The hierarchy $\mathcal{A}$

Self-similarity is packaged as the hierarchy ([[Chapter 1 - Measure Sequences#^def-1-4-2]]):

- $A^{(0)} = \{ \vec{F} \mid \vec{F} \text{ is a } j\text{-sequence for some } j : V \to M \}$;
- $A^{(n+1)} = \{ \vec{F} \in A^{(n)} \mid \forall \alpha\ (0 < \alpha < \mathrm{length}(\vec{F}) \Rightarrow A^{(n)} \cap V_{\kappa(\vec{F})} \in F(\alpha)) \}$;
- $\mathcal{A} = \bigcap_{n < \omega} A^{(n)}$.

A **pleasant** measure sequence is one in which every measure concentrates on measure sequences, which in turn concentrate on measure sequences, "all the way down" — a strong self-similarity. The point: it **costs very little** to assume all $U_J$-sequences are of this type. If $w \in A^{(\infty)}$ and every measure on $w$ concentrates on $A^{(\infty)}$, then by **countable completeness** one can "catch one's tail": everything has a constructing embedding.

With a very modest amount of strength (e.g. $j$ witnessing $(\kappa+1)$-strength), the sequences generated from $j$ are "**extremely pleasant**": measure sequences concentrating on measure sequences consisting of measures which concentrate on measure sequences, etc.

---

## 5. The addability lemma (the one proof done carefully)

This is the lecture's rendition of [[Chapter 1 - Measure Sequences#^lem-1-4-6]], and the speaker performs it as the one careful calculation of the hour.

> **Lemma (addability).** Let $\vec{F} \in \mathcal{A}$ and $A \in \bigcap \vec{F}$. Then
> $$B = \{ w \in A \mid w \text{ is an ordinal, or } \mathrm{length}(w) \geq 1 \text{ and } A \cap V_{\kappa(w)} \in \textstyle\bigcap w \} \in \bigcap \vec{F}.$$

*Proof (as presented).* Fix a constructing embedding $j$ for $\vec{F}$ and verify $B \in F(\alpha)$ for each $\alpha < \mathrm{length}(\vec{F})$, i.e. $\vec{F} \upharpoonright \alpha \in j(B)$.

- **$\alpha = 0$:** $F(0)$ concentrates on ordinals; every ordinal passes the condition of $B$ vacuously; and $\kappa \in j(A)$ since $A \in F(0)$. So $\kappa \in j(B)$.
- **$\alpha \geq 1$:** By elementarity, $j(B)$ is defined by the same formula, so we need:
  1. $\vec{F} \upharpoonright \alpha \in j(A)$ — this is exactly $A \in F(\alpha)$, given;
  2. $j(A) \cap V_\kappa \in \bigcap_{\beta < \alpha} F(\beta)$ — since $j$ fixes $V_\kappa$ pointwise, $j(A) \cap V_\kappa \supseteq j``A = A$, and $A \in F(\beta)$ for every $\beta < \alpha$; upward closure gives the claim.

Hence $\vec{F} \upharpoonright \alpha \in j(B)$ for all $\alpha$, so $B \in \bigcap \vec{F}$. $\blacksquare$

**Terminology introduced:** if $w \in A$ and $A \cap V_{\kappa(w)} \in \bigcap w$, then $w$ is **addable** to $(\vec{F}, A)$.

**Why this matters (foreshadowing).** A Radin condition will be (essentially) a pair consisting of a measure sequence $\vec{F}$ and a set $A$ large for the filter $\bigcap \vec{F}$. Extending the condition means **choosing $w \in A$** and reflecting $A$ down to $A \cap V_{\kappa(w)}$, which is again large for $\bigcap w$. The lemma says there are *many* legal $w$'s — the analogue of the "utterly trivial" fact about Prikry forcing that a condition can be extended by picking any point from its measure-one set.

---

## 6. Summary of where the course is heading

- The **building blocks** of Radin forcing are pairs $(\vec{F}, A)$: a measure sequence $\vec{F} \in \mathcal{A}$ and a set $A \subseteq \mathcal{A}$ with $A \in \bigcap \vec{F}$.
- One-step extension = pick $w \in A$, append it, shrink to $A \cap V_{\kappa(w)}$; the generic object will be a sequence of points of $V_\kappa$ (ordinals and smaller measure sequences), whose first coordinates form a **closed unbounded subset** of $\kappa$ — the *Radin club*.
- The whole theory is a **reflection phenomenon**: a global set $A$ large for a filter reflects to many places below.
- Prikry genericity (diagonalizing one measure) will generalize to a genericity criterion for the more complex Radin generic objects; obtaining them by iteration requires **longer iterations**.
- Generalizations to be mentioned later: supercompact Radin forcing, extended Magidor (interleaving forcings between successive points of the generic sequence — historically used by Gitik–Magidor for $\mathrm{GCH}$ failures everywhere), etc.

---

## Quick terminology index

| Term | Meaning (see [[Chapter 1 - Measure Sequences]] / [[Chapter 2 - The Radin Forcing]]) |
| --- | --- |
| **measure sequence** | $j$-sequence of ultrafilters on $V_\kappa$, all derived from one embedding (Def 1.1.1, 1.4.1) |
| **weak measure sequence (wms)** | $\langle \kappa(w) \rangle^\frown \langle w(\alpha)\rangle$, $\kappa(w)$ inaccessible, $w(0)$ normal (Def 1.2.1) |
| **constructing embedding** | an embedding witnessing that a sequence is a measure sequence (Def 1.4.1) |
| **$\mathcal{A}$** | $\bigcap_{n<\omega} A^{(n)}$, the reservoir of building blocks (Def 1.4.2) |
| **$\bigcap \vec{F}$** | intersection filter of all measures on $\vec{F}$ (Def 1.4.4) |
| **diagonal intersection** | $\Delta_{x \in V_\kappa} A_x = \{w \mid \forall x \in V_{\kappa(w)}\ (w \in A_x)\}$ (Def 1.3.1) |
| **repeat point** | a stage in the construction of the sequence "where you have seen everything" |
| **addability** | $w \in A$ is addable to $(\vec{F}, A)$ iff $A \cap V_{\kappa(w)} \in \bigcap w$ (Lemma 1.4.6) |
| **Prikry forcing** | the $\mathrm{length}(\vec{F}) = 1$ case of Radin forcing (Prop 2.3.1) |

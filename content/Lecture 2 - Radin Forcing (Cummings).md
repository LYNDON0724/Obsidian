# Lecture 2 — Radin Forcing: Conditions, Ordering, and the Dictionary

> [!info] Source
> - **Speaker:** James Cummings
> - **Series:** Simons Semester "Gödel's Program", Banach Center, Warsaw — *Radin Forcing (Lecture 2)*, 1h 01m
> - **Video (local):** `Cummings Lectures/Radin Forcing (Lecture 2).mp4`
> - **Note:** These notes are reconstructed from an automatic transcript, cross-checked against [[Chapter 2 - The Radin Forcing]] (whose numbering and notation are followed). This lecture is the *formal definition* lecture: conditions, the two orders, the generic-filter/generic-sequence dictionary, and a preview of the Prikry property and factorization.

---

## 0. ⚠️ Convention mismatch: the meaning of "length"

The lecture's `length` counts the *entry* $\kappa$ itself, so its numbering is **off by one** from [[Chapter 2 - The Radin Forcing|Chapter 2]]:

|                             | lecture convention | Chapter 2 convention                                                         |                  |
| --------------------------- | ------------------ | ---------------------------------------------------------------------------- | ---------------- |
| no measures (just $\kappa$) | length $1$         | length $0$ — **not used** as a parameter                                     |                  |
| one measure                 | length $2$         | **length $1$** = Prikry forcing ([[Chapter 2 - The Radin Forcing#^prop-2-3-1\|Prop 2.3.1]])    |
| two measures                | length $3$         | length $2$ ([[Chapter 2 - The Radin Forcing#^exmp-2-3-2\| Example 2.3.2]]) |

Everything below is stated in the **Chapter 2 convention** (length = number of measures); the lecture's sentences are translated accordingly.

---

## 1. The parameter and the trivial case

- Radin forcing $R_{\vec{V}}$ is defined from a measure sequence $\vec{V} \in \mathcal{A}$ with **at least one measure**, i.e. $\mathrm{length}(\vec{V}) \geq 1$ in the Chapter 2 convention.
- **Why exclude length $0$:** a sequence with no measures carries no constraints; its "filter" $\bigcap \vec{V}$ is degenerate (the empty set counts as large — a purely technical convention, since there are no measures to be large for). A condition whose top is such a sequence would have its top constraint set forced to be empty — a trivial, "rubbish" forcing.
- It is *tempting* to think that with exactly one measure we are simply defining Prikry forcing. The lecture warns: **"that isn't quite right"** — see §5.

## 2. What the generic object is supposed to look like

As with Prikry forcing, the lecture first declares the intended shape of the generic object (this is "the same spirit" as saying *the generic object is a cofinal $\omega$-sequence in $\kappa$* before defining Prikry conditions):

- The generic object of $R_{\vec{V}}$ is a **sequence of measure sequences**: its points are ordinals and smaller measure sequences, with **strictly increasing, continuous and cofinal associated critical points** in $\kappa$.
- Because it is a *sequence of sequences*, indexing is a pain: **subscripts** say where you are along the generic sequence, **superscripts** say which measure *inside* a sequence you mean. The lecture stresses being scrupulous about this convention.
- Useful intuition: a Radin generic sequence is like writing your favourite well-order as a **direct limit of finite linear orders** — each condition pins down finitely many points, and the conditions "weave together" into the generic object.
- A typical Radin generic has a strictly increasing, continuous, cofinal sequence of critical points; the points of $V_\kappa$ occurring in it are its **first coordinates** (the Radin club of [[Chapter 3 - The Radin Club and Changes of Cofinality#^def-3-1-1|Chapter 3]]).

**The spectrum of possible order types.** The order type of the generic sequence is *not* forced to be $\omega$. There are two regimes:

- **Short parameter:** by forcing below carefully chosen conditions one can **tune** the order type (e.g. make it $\omega_1$ — see §9).
- **Long parameter:** once $\mathrm{length}(\vec{V})$ is large enough to *preserve* large cardinal properties of $\kappa$, the generic sequence **must** have order type $\kappa$ — otherwise it would singularize $\kappa$, militating against preserving it as a large cardinal (the regime of [[Chapter 4 - Preserving Large Cardinals|Chapter 4]]).

## 3. Conditions (Definition 2.2.1 in words)

A condition $p$ is a finite sequence of **pairs** (a measure sequence, a large set) followed by the top:

$$p = \langle (u_1, A_1), \dots, (u_n, A_n), \langle \kappa, \vec{V} \rangle, A \rangle$$

- Each $A_i$ is **large for the filter** $\bigcap u_i$ ([[Chapter 1 - Measure Sequences#^def-1-4-4|Def 1.4.4]]); the top $A \in \bigcap \vec{V}$.
- The critical points $\kappa(u_i)$ are **strictly increasing**; the last entry is always the parameter $\vec{V}$ itself (the top).
- If some $u_i$ has length $0$ (no measures), then $A_i$ **must be empty**; such $u_i$ are destined to become **zero or successor points** of the generic sequence. Measure sequences carrying measures occupy the "living" positions (the limit points).
- The weakest condition is just $\langle \langle \kappa, \vec{V} \rangle, \mathcal{A} \cap V_\kappa \rangle$ — everything reasonable allowed, nothing specified.

**What a condition commits you to** (the philosophy, verbatim the same as Prikry):
1. Every non-top sequence $u_i$ in the stem **appears somewhere on the generic sequence**;
2. Anything that eventually appears on the generic sequence **between $u_i$ and $u_{i+1}$** must be drawn from $A_i$.

> [!note] Large ≠ concentrated
> A condition only says $A$ is *large for the filter*. That is **not** the same as $A$ containing some natural set on which the filter concentrates. The distinction matters: e.g. if $\mathrm{length}(\vec{V}) = 2$, $U(1)$ concentrates on pairs, but a large set need not be contained in the "natural" concentrated family; forcing below such sets can produce order types that look surprising. This is a genuine phenomenon, not an artefact.

## 4. The ordering and the two elementary moves (Definitions 2.2.2–2.2.3)

$q \leq p$ (q stronger) requires:

- same top $\vec{V}$; every measure sequence that $p$ committed to still appears in $q$'s stem;
- for each sequence already in $p$'s stem (i.e. $v_j = u_i$), the constraint set of $q$ is **at least as strong**: $B_j \subseteq A_i$;
- new entries are **insertions**: a new pair interpolated between $u_i$ and $u_{i+1}$ must have its measure sequence drawn from the next large set $A_i$, and its own large set contained in $A_i$.

**Two elementary extension moves**, and every extension is a finite composition of them:

1. **Shrink** an $A_i$ (and the blocks of stem triples);
2. **Interpolate** a new pair between two old pairs (or below the first old pair), obeying: the new sequence is drawn from the next large set, and its large set is contained in that next large set.

This mirrors the two-phase picture of Prikry extensions: first add the new points to the stem, then shrink the constraint sets.

*Important caveat:* one must **not** say that new sequences come from "higher" large sets — later $A_i$'s may be empty and may shrink during extensions. The unique occurrence of each $v_j$ among the $u_i$'s is guaranteed by the strictly increasing critical points.

If **all** $u_i$ are single points (length $0$), then all $A_i$ are empty except the top — this is exactly the Prikry special case.

## 5. The one-measure case: why it is "not quite" Prikry (Proposition 2.3.1)

If $\vec{V} = \langle \kappa, U \rangle$ (length $1$), then everything below the top is just a single sequence with the empty set, and the top is essentially a measure-one set for $U$ — *this is how one recalls Prikry forcing*.

But the lecture insists: exactly one measure does **not** literally give Prikry forcing. The reason is precisely the remark after [[Chapter 2 - The Radin Forcing#^prop-2-3-1|Prop 2.3.1]]: $R_{\langle \kappa, U \rangle}$ consists of the Prikry part *together with* **side copies of smaller Radin forcings** sitting below measurable cardinals $\nu < \kappa$ (conditions whose stems contain genuine triples coming from smaller measure sequences, incompatible with the "pure Prikry" condition). So the length-$1$ forcing is Prikry forcing **plus autonomous substructures below**.

## 6. The dictionary: generic filter ↔ generic sequence

Exactly as in Prikry forcing ("day one of Prikry school"), there is a translation between the generic object as a *filter* and as a *sequence*:

- **Filter → sequence:** collect all measure sequences appearing as first coordinates of pairs in the stems of conditions of $G$. (Careful: "appears" means *as the first entry of some pair* in some condition of $G$.)
- **Sequence → filter:** a condition belongs to the filter iff its stem is an **initial segment** of the generic sequence, and everything in the generic sequence beyond the stem lies in the top large set.

**Addability (audibility).** A condition $p$ should not rule out a point $w$ appearing on the generic sequence; such a $w$ is **addable** to $p$ in the sense of [[Chapter 1 - Measure Sequences#^lem-1-4-6|Lemma 1.4.6]]: $w \in A$ and $A \cap V_{\kappa(w)} \in \bigcap w$. (All $w$'s in play have $\kappa(w) < \kappa$ — the rules of the game.)

**What a generic filter is morally:** conditions of $G$ are *non-restrictive* — anything a condition insists on being on the sequence really is on the sequence — and *permissive* — anything not excluded by the constraints can be extended to the next step. This is the same "constraints on what may appear" philosophy as Prikry.

## 7. Diagonal intersections: the canonical move

The reason the lecture was at pains to have the **generalized diagonal intersection** ([[Chapter 1 - Measure Sequences#^def-1-3-1|Def 1.3.1]]) is that it is an absolutely typical move in the theory:

> Given a family of large sets $\langle A_x \mid x \in V_\kappa \rangle$ indexed by potential roles, form the diagonal intersection $\Delta_x A_x$. It is large, and moreover any $w \in \Delta_x A_x$ has every "fitting" $s$ (with $\kappa(s) < \kappa(w)$) in the corresponding $A_s$.

This is the engine behind every "shrink so that everything inside is addable" argument (the addability lemma in action).

## 8. The Prikry property and factorization: preview (Section 2.4)

**Prikry property** ([[Chapter 2 - The Radin Forcing#^lem-2-4-4|Lemma 2.4.4]]): given any condition and any sentence $\sigma$ of the forcing language, there is a **pure / direct extension** (shrink the $A_i$'s only — no interpolation) deciding $\sigma$. This is the good news.

**Why "no bounded subsets of $\kappa$" needs work:** in ordinary Prikry forcing there is one measure-one set at the top, large for a $\kappa$-complete measure — so the proof that no bounded subsets of $\kappa$ are added is trivial. A typical Radin condition, by contrast, has a stem containing **many measure-one sets for measures living on smaller critical points**, whose completeness is only for smaller cardinals. One must therefore apply the Prikry property *in an ingenious way* to control bounded subsets.

**Factorization** ([[Chapter 2 - The Radin Forcing#^lem-2-4-2|Lemma 2.4.2]]): the definition of extension is **very local** — the rules about interpolation depend only on the *next* measure-one set. Consequently, below any condition, $R_{\vec{V}}$ factors in many ways into a **high part × low part**, each factor being a Radin forcing in its own right. Moreover the measures in the high part are very complete — complete beyond the cardinality of even the regular open algebra of the low part. This is what controls the bounded subsets of $\kappa$:

> Every bounded subset of $\kappa$ added by $R_{\vec{V}}$ lives in the extension generated by a **strict initial segment** of the generic sequence.

(That statement is the content of the cardinal-preservation argument, [[Chapter 2 - The Radin Forcing#^thm-2-4-5|Theorem 2.4.5]].)

## 9. Tuning the order type: the $\omega_1$ example

The lecture answers a question about the relation between the order type $\lambda$ of the generic sequence and $\kappa$: **it depends** — on the length of the parameter and on the condition you force below.

**Recipe for order type $\omega_1$:** construct a measure sequence $\vec{V}$ of length $\omega_1$. By self-similarity ([[Chapter 3 - The Radin Club and Changes of Cofinality#^ex-3-2-2|Exercise 3.2.2]]: $X_\tau \in U(\tau)$), the set of measure sequences of **countable length** is large for the associated filter: $A = \bigcup_{\tau < \omega_1} X_\tau \in \bigcap \vec{V}$. Forcing below the condition $\langle \langle \kappa, \vec{V} \rangle, A \rangle$, every pair entering the generic sequence has countable length, so the Radin club has order type $\omega^{\omega_1} = \omega_1$ — cf. the order-type computation of [[Chapter 3 - The Radin Club and Changes of Cofinality#^thm-3-2-5|Theorem 3.2.5]]. So with a short sequence one can *tune* the cofinality change; with a long enough sequence (preserving large cardinals) the order type is forced to be $\kappa$.

## 10. Magidor forcing, and where the course is going

- **Magidor forcing** lets one singularize a large cardinal $\kappa$ to your favourite (uncountable) cofinality in a pretty way — and **the same effect is achievable with Radin forcing**. Historically Magidor did *not* build his forcing from a coherent sequence of measures; with hindsight that might have been the best thing to do (cf. [[Chapter 5 - Coherent Sequences of Measures|Chapter 5]]).
- There is a **generic iteration** for Radin forcing and one for Magidor forcing; "if you really squint, you can see the forcings are operating in slightly different ways by looking at the iterations that give rise to them".
- **Next (afternoon session):** the regime where a sufficiently long measure sequence **preserves large cardinal properties of $\kappa$** — the subject of [[Chapter 4 - Preserving Large Cardinals|Chapter 4]].

---

## Quick terminology index

| Term | Meaning |
| --- | --- |
| **stem** | the finite sequence of pairs below the top in a condition |
| **top** | the last entry $\langle \kappa, \vec{V} \rangle$ — always the parameter |
| **measure-one set** | the top constraint set $A \in \bigcap \vec{V}$ |
| **large for the filter** | $A_i \in \bigcap u_i$ — weaker than "concentrates on" |
| **direct / pure extension** | $\leq^*$: same stem, only constraint sets shrunk ([[Chapter 2 - The Radin Forcing#^def-2-2-3|Def 2.2.3]]) |
| **interpolation** | inserting a new pair drawn from the next large set, its own large set contained in that one |
| **addable** | $w \in A$ and $A \cap V_{\kappa(w)} \in \bigcap w$ ([[Chapter 1 - Measure Sequences#^lem-1-4-6|Lemma 1.4.6]]) |
| **dictionary** | filter → sequence: collect stem first-coordinates; sequence → filter: initial segments + tail in top set |
| **Radin club** | first coordinates of stem entries, club in $\kappa$ ([[Chapter 3 - The Radin Club and Changes of Cofinality#^def-3-1-1|Chapter 3]]) |
